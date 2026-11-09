#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/http/bindings
         web-server/http/redirect
         net/url
         net/base64
         file/sha1
         json
         db
         racket/draw
         racket/math
         racket/sandbox
         xml)

;; ---------------------------------------------------------------------------
;; Resource / safety limits.  The DSL is a public, unauthenticated endpoint, so
;; every input is treated as hostile.  These caps bound CPU + memory so that no
;; single request can take down the process (and, together with the systemd
;; sandbox, the host).
;; ---------------------------------------------------------------------------
(define PORT            (let ([p (getenv "RACKET_APP_PORT")])
                          (or (and p (string->number p)) 8345)))
(define MAX-CODE-LENGTH 100000)          ; chars of DSL source accepted
(define MAX-UPLOAD-BYTES (* 3 1024 1024)) ; 3 MB image upload (nginx is the real gate)
(define MAX-ELEMENTS    6000)            ; total SVG nodes a single render may emit
(define MAX-REPEAT      2000)            ; iterations a single (repeat ...) may run
(define MAX-DEPTH       24)              ; command nesting depth
(define MAX-EXPR-DEPTH  40)              ; arithmetic expression nesting depth
(define MAX-NUMBER      1e7)             ; magnitude clamp for every computed number
(define MAX-RANDOM      1000000)         ; upper bound handed to (random ...)
;; The element budget above only bounds *emitted shapes*.  These additionally
;; bound raw work and total output so that inputs which never emit a shape
;; (invalid commands, empty `let` bodies, giant arithmetic) and point-heavy
;; shapes (polygons/polylines/stars) are still bounded.  `call-with-limits`
;; is the hard backstop: even an unforeseen path cannot exceed these.
(define MAX-FUEL        2500000)         ; work units (expr nodes + iterations + points) per render
(define MAX-TOTAL-POINTS 24000)          ; total polygon/polyline/star vertices per render (bounds output size)
(define RENDER-TIME-SEC 3)               ; hard wall-clock backstop per render (seconds)
(define RENDER-MEM-MB   96)              ; hard per-render memory backstop (MB)

;; ---------------------------------------------------------------------------
;; Numbers
;; ---------------------------------------------------------------------------

;; Keep every value finite and bounded so arithmetic can't blow up into huge
;; bignums / infinities that would stall number->string or the renderer.
(define (clamp-num n)
  (cond
    [(not (real? n)) 0]
    [(and (flonum? n) (or (nan? n) (infinite? n))) 0]
    [(> n MAX-NUMBER) MAX-NUMBER]
    [(< n (- MAX-NUMBER)) (- MAX-NUMBER)]
    [else n]))

;; Render a number for an SVG attribute: never emit exact rationals like "1/3"
;; (invalid in SVG) or unbounded decimals.
(define (fmt-num v)
  (define n (clamp-num (if (number? v) v 0)))
  (define f (exact->inexact n))
  (if (integer? f)
      (number->string (inexact->exact f))
      (~r f #:precision 3)))

;; Real-valued modulo that also works on flonums (SVG art wants tiling).
(define (safe-mod a b)
  (if (zero? b) 0 (- a (* b (floor (/ a b))))))

;; Base environment: named constants available to every expression.  `i` is
;; injected by `repeat` as the loop index; `let` extends this with locals.
(define BASE-ENV (hasheq 'pi pi 'tau (* 2 pi) 'width 600 'height 400))

;; Safe numeric evaluator for the arithmetic sub-language.  Bounded in both
;; recursion depth and value magnitude; symbols resolve against `env`; every
;; unknown form evaluates to 0 rather than raising.  Every node also burns one
;; unit of the shared fuel budget, so an expression like (+ 1 1 1 ... 20000x)
;; or a loop body that only computes cannot run unbounded work.
(define (eval-num v env [depth 0])
  (burn! 1)
  (define (ev x) (eval-num x env (add1 depth)))
  (cond
    [(not (fuel-left? (current-ctx))) 0]
    [(> depth MAX-EXPR-DEPTH) 0]
    [(number? v) (clamp-num (if (real? v) v 0))]
    [(symbol? v) (let ([r (hash-ref env v 0)]) (clamp-num (if (real? r) r 0)))]
    [(pair? v)
     (clamp-num
      (match v
        [(list 'random n)
         (let ([m (inexact->exact (floor (max 0 (ev n))))])
           (if (<= m 0) 0 (random (min m MAX-RANDOM))))]
        [(list 'random a b)
         (let ([lo (inexact->exact (floor (ev a)))]
               [hi (inexact->exact (floor (ev b)))])
           (if (< lo hi) (+ lo (random (min (- hi lo) MAX-RANDOM))) lo))]
        [(cons '+ args)              (for/sum     ([x (in-list args)]) (ev x))]
        [(cons '* args)              (for/product ([x (in-list args)]) (ev x))]
        [(list '- a)                 (- (ev a))]
        [(cons '- (cons a rest))     (- (ev a) (for/sum ([x (in-list rest)]) (ev x)))]
        [(list '/ a b)               (let ([d (ev b)]) (if (zero? d) 0 (/ (ev a) d)))]
        [(list 'mod a b)             (safe-mod (ev a) (ev b))]
        [(list 'pow a b)             (let ([base (ev a)] [e (max -8 (min 8 (ev b)))])
                                       ;; Guard every exponent case that raises or blows up:
                                       ;; negative/fractional powers of non-positive bases, and
                                       ;; exact-bignum growth (coerce the base to a flonum).
                                       (cond [(and (<= base 0) (not (integer? e))) 0]
                                             [(and (zero? base) (< e 0)) 0]
                                             [else (expt (exact->inexact base) e)]))]
        [(list 'sin a)               (sin (ev a))]
        [(list 'cos a)               (cos (ev a))]
        [(list 'tan a)               (let ([c (cos (ev a))]) (if (zero? c) 0 (/ (sin (ev a)) c)))]
        [(list 'sqrt a)              (let ([x (ev a)]) (if (< x 0) 0 (sqrt x)))]
        [(list 'abs a)               (abs (ev a))]
        [(list 'neg a)               (- (ev a))]
        [(list 'floor a)             (floor (ev a))]
        [(list 'round a)             (round (ev a))]
        [(list 'ceil a)              (ceiling (ev a))]
        [(list 'sign a)              (let ([x (ev a)]) (cond [(> x 0) 1] [(< x 0) -1] [else 0]))]
        [(list 'exp a)               (exp (min 30 (ev a)))]           ; clamp-num caps the result
        [(list 'log a)               (let ([x (ev a)]) (if (<= x 0) 0 (log x)))]
        [(list 'atan a)              (atan (ev a))]
        [(list 'atan2 a b)           (atan (ev a) (ev b))]
        [(list 'hypot a b)           (let ([x (ev a)] [y (ev b)]) (sqrt (+ (* x x) (* y y))))]
        [(list 'dist a b c d)        (let ([dx (- (ev c) (ev a))] [dy (- (ev d) (ev b))])
                                       (sqrt (+ (* dx dx) (* dy dy))))]
        [(list 'lerp a b t)          (let ([x (ev a)] [y (ev b)] [u (ev t)]) (+ x (* (- y x) u)))]
        [(list 'clamp a lo hi)       (let ([x (ev a)] [l (ev lo)] [h (ev hi)]) (max (min l h) (min (max l h) x)))]
        ;; (map v in-lo in-hi out-lo out-hi): remap v from one range to another.
        [(list 'map v il ih ol oh)   (let ([x (ev v)] [a (ev il)] [b (ev ih)] [c (ev ol)] [d (ev oh)])
                                       (if (= a b) c (+ c (* (/ (- x a) (- b a)) (- d c)))))]
        [(list 'noise a)             (value-noise (ev a) 0.0)]
        [(list 'noise a b)           (value-noise (ev a) (ev b))]
        [(list 'noise a b c)         (value-noise (+ (ev a) (* 131.0 (ev c))) (ev b))]
        [(cons 'min (and args (cons _ _))) (apply min (map ev args))]
        [(cons 'max (and args (cons _ _))) (apply max (map ev args))]
        [_ 0]))]
    [else 0]))

;; ---------------------------------------------------------------------------
;; Value noise — deterministic, smooth pseudo-random field in [0,1], the
;; backbone of organic procedural art (terrain, clouds, flow fields).  Pure
;; integer hashing + smoothstep bilinear interpolation: O(1), no state, fully
;; reproducible for a given seed.
;; ---------------------------------------------------------------------------
(define (hash-01 ix iy)
  (define n (bitwise-and (+ (* ix 374761393) (* iy 668265263)) #xffffffff))
  (define m (bitwise-and (* (bitwise-xor n (arithmetic-shift n -13)) 1274126177) #xffffffff))
  (/ (exact->inexact (bitwise-and (bitwise-xor m (arithmetic-shift m -16)) #xffffff)) 16777215.0))

(define (value-noise x y)
  (define (smooth t) (* t t (- 3.0 (* 2.0 t))))
  (define x0 (floor x)) (define y0 (floor y))
  (define ix (inexact->exact x0)) (define iy (inexact->exact y0))
  (define ux (smooth (- x x0))) (define uy (smooth (- y y0)))
  (define a (hash-01 ix iy))            (define b (hash-01 (add1 ix) iy))
  (define c (hash-01 ix (add1 iy)))     (define d (hash-01 (add1 ix) (add1 iy)))
  (+ (* a (- 1.0 ux) (- 1.0 uy)) (* b ux (- 1.0 uy))
     (* c (- 1.0 ux) uy)         (* d ux uy)))

;; ---------------------------------------------------------------------------
;; Colors — validated against a conservative whitelist.  xexpr->string already
;; escapes attribute values (so this is not the XSS boundary), but rejecting
;; junk keeps the SVG well-formed and blocks any attribute-context surprises.
;; ---------------------------------------------------------------------------
(define color-rx
  #px"^(#[0-9a-fA-F]{3,8}|rgba?\\([-0-9.,%[:space:]]+\\)|hsla?\\([-0-9.,%[:space:]]+\\)|[a-zA-Z]{1,20})$")

(define (clamp-255 x)  (max 0   (min 255 (inexact->exact (round x)))))
(define (clamp-pct x)  (max 0   (min 100 (inexact->exact (round x)))))
(define (clamp-360 x)  (modulo (inexact->exact (round x)) 360))
(define (clamp-unit x) (~r (max 0.0 (min 1.0 (exact->inexact x))) #:precision 3))

;; Colors may be a literal string (validated against the whitelist) or a
;; computed builder — (rgb r g b), (rgba r g b a), (hsl h s l), (hsla h s l a) —
;; whose numeric parts are evaluated and hard-clamped to valid CSS ranges.
(define (eval-color c env [fallback "#ff79c6"])
  (define (ev x) (eval-num x env))
  (match c
    [(? string?)
     (define s (string-trim c))
     (if (and (<= (string-length s) 40) (regexp-match? color-rx s)) s fallback)]
    [(list 'rgb r g b)      (format "rgb(~a,~a,~a)"        (clamp-255 (ev r)) (clamp-255 (ev g)) (clamp-255 (ev b)))]
    [(list 'rgba r g b a)   (format "rgba(~a,~a,~a,~a)"    (clamp-255 (ev r)) (clamp-255 (ev g)) (clamp-255 (ev b)) (clamp-unit (ev a)))]
    [(list 'hsl h s l)      (format "hsl(~a,~a%,~a%)"      (clamp-360 (ev h)) (clamp-pct (ev s)) (clamp-pct (ev l)))]
    [(list 'hsla h s l a)   (format "hsla(~a,~a%,~a%,~a)"  (clamp-360 (ev h)) (clamp-pct (ev s)) (clamp-pct (ev l)) (clamp-unit (ev a)))]
    ;; (hsv h s v): hue 0..360, saturation/value 0..100 — handy for vivid art.
    [(list 'hsv h s v)      (match-define (list r g b) (hsv->rgb (ev h) (ev s) (ev v))) (format "rgb(~a,~a,~a)" r g b)]
    ;; (palette "name" i): pick a curated color by index.
    [(list 'palette (? string? name) i) (palette-color name (ev i))]
    ;; Per-shape gradient paints: usable anywhere a color is (fill of any shape).
    ;; (linear angle c1 c2 ...) and (radial c1 c2 ...) register a gradient in
    ;; objectBoundingBox units and return its url(#id).
    [(list* 'linear angle (and cs (cons _ _)))
     (gradient-url 'linear cs env
                   (list `(gradientTransform ,(format "rotate(~a 0.5 0.5)" (fmt-num (ev angle))))))]
    [(list* 'radial (and cs (cons _ _)))
     (gradient-url 'radial cs env)]
    ;; (mix c1 c2 t): linear RGB interpolation between any two colors at t in
    ;; [0,1] — smooth gradients across a loop without SVG <defs>.
    [(list 'mix c1 c2 t)    (match-define (list r g b) (mix-rgb c1 c2 (ev t) env)) (format "rgb(~a,~a,~a)" r g b)]
    [_ fallback]))

;; --- color -> (r g b) for interpolation --------------------------------------
;; A small table of the CSS names worth interpolating; any other name falls
;; back to mid-gray (it still renders fine as a literal via eval-color).
(define CSS-NAMED
  (hash "black" '(0 0 0) "white" '(255 255 255) "red" '(255 0 0) "lime" '(0 255 0)
        "green" '(0 128 0) "blue" '(0 0 255) "yellow" '(255 255 0) "cyan" '(0 255 255)
        "magenta" '(255 0 255) "orange" '(255 165 0) "purple" '(128 0 128)
        "pink" '(255 192 203) "gray" '(128 128 128) "grey" '(128 128 128)
        "navy" '(0 0 128) "teal" '(0 128 128) "gold" '(255 215 0) "tomato" '(255 99 71)
        "coral" '(255 127 80) "indigo" '(75 0 130) "violet" '(238 130 238)))

;; Named palettes — (palette "name" i) cycles through curated colors, so good
;; art is one call away.  Unknown names fall back to a neutral ramp.
(define PALETTES
  (hash "fire"   (vector "#2b0a00" "#7a1500" "#d13300" "#ff6a00" "#ffb300" "#ffe066")
        "ocean"  (vector "#021d2e" "#063a53" "#0a6f8f" "#18a7c0" "#5fd3d8" "#bff3ee")
        "neon"   (vector "#ff2a6d" "#d300c5" "#7700ff" "#00e5ff" "#39ff14" "#f5ff00")
        "pastel" (vector "#ffd1dc" "#ffe7c2" "#fff5ba" "#d4f0c0" "#c7e9ff" "#e3d1ff")
        "sunset" (vector "#0d1b2a" "#3b185f" "#88307a" "#d34e8c" "#ff7e5f" "#ffd080")
        "forest" (vector "#06230f" "#114d2a" "#2e7d32" "#66bb6a" "#aed581" "#e6ee9c")
        "mono"   (vector "#111111" "#444444" "#777777" "#aaaaaa" "#dddddd" "#ffffff")))

(define (palette-color name i)
  (define v (hash-ref PALETTES (string-downcase (string-trim name)) #f))
  (if v (vector-ref v (modulo (inexact->exact (floor i)) (vector-length v))) "#888888"))

(define (hex->rgb s)
  (define h (substring s 1))
  (define (pair i) (string->number (substring h i (+ i 2)) 16))
  (define (dup i) (let ([v (string->number (substring h i (+ i 1)) 16)]) (and v (+ (* v 16) v))))
  (cond [(= (string-length h) 3) (map (lambda (i) (or (dup i) 0)) '(0 1 2))]
        [(>= (string-length h) 6) (map (lambda (i) (or (pair i) 0)) '(0 2 4))]
        [else '(128 128 128)]))

(define (hsl->rgb h s l)
  (define hh (/ (modulo (inexact->exact (round h)) 360) 360.0))
  (define ss (/ (max 0.0 (min 100.0 (exact->inexact s))) 100.0))
  (define ll (/ (max 0.0 (min 100.0 (exact->inexact l))) 100.0))
  (define (hue->c p q t0)
    (define t (cond [(< t0 0) (+ t0 1)] [(> t0 1) (- t0 1)] [else t0]))
    (cond [(< t (/ 1.0 6)) (+ p (* (- q p) 6 t))]
          [(< t 0.5) q]
          [(< t (/ 2.0 3)) (+ p (* (- q p) (- (/ 2.0 3) t) 6))]
          [else p]))
  (cond [(= ss 0) (list (clamp-255 (* ll 255)) (clamp-255 (* ll 255)) (clamp-255 (* ll 255)))]
        [else (define q (if (< ll 0.5) (* ll (+ 1 ss)) (- (+ ll ss) (* ll ss))))
              (define p (- (* 2 ll) q))
              (list (clamp-255 (* 255 (hue->c p q (+ hh (/ 1.0 3)))))
                    (clamp-255 (* 255 (hue->c p q hh)))
                    (clamp-255 (* 255 (hue->c p q (- hh (/ 1.0 3))))))]))

(define (hsv->rgb h s v)
  (define hh (/ (modulo (inexact->exact (round h)) 360) 60.0))
  (define ss (/ (max 0.0 (min 100.0 (exact->inexact s))) 100.0))
  (define vv (/ (max 0.0 (min 100.0 (exact->inexact v))) 100.0))
  (define c (* vv ss))
  (define x (* c (- 1 (abs (- (- hh (* 2 (floor (/ hh 2)))) 1)))))
  (define m (- vv c))
  (define-values (r1 g1 b1)
    (cond [(< hh 1) (values c x 0)] [(< hh 2) (values x c 0)]
          [(< hh 3) (values 0 c x)] [(< hh 4) (values 0 x c)]
          [(< hh 5) (values x 0 c)] [else (values c 0 x)]))
  (list (clamp-255 (* 255 (+ r1 m))) (clamp-255 (* 255 (+ g1 m))) (clamp-255 (* 255 (+ b1 m)))))

(define (color->rgb c env)
  (define (ev x) (eval-num x env))
  (match c
    [(list 'rgb r g b)     (list (clamp-255 (ev r)) (clamp-255 (ev g)) (clamp-255 (ev b)))]
    [(list 'rgba r g b _)  (list (clamp-255 (ev r)) (clamp-255 (ev g)) (clamp-255 (ev b)))]
    [(list 'hsl h s l)     (hsl->rgb (ev h) (ev s) (ev l))]
    [(list 'hsla h s l _)  (hsl->rgb (ev h) (ev s) (ev l))]
    [(list 'hsv h s v)     (hsv->rgb (ev h) (ev s) (ev v))]
    [(list 'palette (? string? name) i) (hex->rgb (palette-color name (ev i)))]
    [(list 'mix c1 c2 t)   (mix-rgb c1 c2 (ev t) env)]
    [(? string?) (let ([s (string-downcase (string-trim c))])
                   (cond [(regexp-match? #px"^#[0-9a-fA-F]{3,8}$" s) (hex->rgb s)]
                         [(hash-ref CSS-NAMED s #f) => values]
                         [else '(128 128 128)]))]
    [_ '(128 128 128)]))

(define (mix-rgb c1 c2 t env)
  (define u (max 0.0 (min 1.0 (exact->inexact t))))
  (for/list ([a (in-list (color->rgb c1 env))] [b (in-list (color->rgb c2 env))])
    (clamp-255 (+ a (* (- b a) u)))))

;; ---------------------------------------------------------------------------
;; Render context: a shared, mutable budget so total emitted nodes are capped
;; regardless of how the commands are nested.
;; ---------------------------------------------------------------------------
;;   budget — shapes still allowed to emit   (caps element count)
;;   fuel   — raw work units still allowed    (caps CPU regardless of shapes)
;;   points — polygon/polyline/star vertices  (caps output size)
;;   errors — error nodes already emitted     (caps error-node spam)
;;   defs   — accumulated <defs> children (gradients/filters), newest first
;;   gid    — monotonic id counter for generated ids
;;   defcache — dedup identical filter defs so repeated effects share one <filter>
(struct rctx (budget fuel points errors defs gid defcache) #:mutable)
(define (make-rctx) (rctx MAX-ELEMENTS MAX-FUEL MAX-TOTAL-POINTS 0 '() 0 (make-hash)))

;; A parameter holding the live context, so the numeric evaluator and the
;; geometry helpers can charge the shared budget without threading ctx through
;; every signature.  The default is a fresh full budget (only reached by stray
;; calls outside a render; real renders parameterize it).
(define current-ctx (make-parameter (make-rctx)))

(define (budget-left? ctx) (> (rctx-budget ctx) 0))
(define (fuel-left?   ctx) (> (rctx-fuel   ctx) 0))
;; A render is "alive" while it still has both shapes and work left.
(define (alive? ctx) (and (budget-left? ctx) (fuel-left? ctx)))
(define (spend! ctx) (set-rctx-budget! ctx (sub1 (rctx-budget ctx))))

;; Burn `n` work units against the current context's fuel.
(define (burn! [n 1])
  (define c (current-ctx))
  (set-rctx-fuel! c (- (rctx-fuel c) n)))

;; Claim one output vertex; #f once the per-render vertex budget is spent, so
;; point-heavy shapes truncate instead of ballooning the serialized SVG.
(define (take-point!)
  (define c (current-ctx))
  (and (> (rctx-points c) 0)
       (begin (set-rctx-points! c (sub1 (rctx-points c))) #t)))

;; Register a <defs> child (a gradient) and return the generated id to
;; reference it with fill="url(#id)".  Bounded by the element budget.
(define (add-def! make-node)
  (define c (current-ctx))
  (define id (format "g~a" (rctx-gid c)))
  (set-rctx-gid! c (add1 (rctx-gid c)))
  (set-rctx-defs! c (cons (make-node id) (rctx-defs c)))
  id)

(define (short-str s)
  (define str (format "~a" s))
  (if (> (string-length str) 200) (string-append (substring str 0 200) "…") str))

(define (err-node label msg y)
  (list `(text ((x "12") (y ,(number->string y)) (fill "#ff5555")
                (font-family "monospace") (font-size "13"))
               ,(string-append label ": " (short-str msg)))))

;; An error still emits a node, so it costs element budget (stops floods of
;; invalid commands at the element cap).  Only the first MAX-ERROR-NODES are
;; actually rendered — beyond that they are counted and dropped, so a hostile
;; "all invalid" program can't balloon the output with thousands of red texts.
(define MAX-ERROR-NODES 24)
(define (note-error! ctx label msg base-y)
  (spend! ctx)
  (set-rctx-errors! ctx (add1 (rctx-errors ctx)))
  (define k (rctx-errors ctx))
  (if (<= k MAX-ERROR-NODES)
      (err-node label msg (min 392 (+ base-y (* (sub1 k) 15))))
      '()))

;; Cap text length so a single (text ...) node can't carry a megabyte of glyphs.
(define MAX-TEXT-LEN 300)
(define (clip-text s)
  (if (> (string-length s) MAX-TEXT-LEN) (substring s 0 MAX-TEXT-LEN) s))

;; Turn a flat list of coordinate expressions into an SVG "x,y x,y ..." string.
;; Points are capped so a giant coordinate list can't bloat one element.
(define MAX-POINTS 1200)
(define (points->str exprs env)
  (define nums (for/list ([e (in-list exprs)] [_ (in-range (* 2 MAX-POINTS))]
                          #:break (not (fuel-left? (current-ctx))))
                 (eval-num e env)))
  (let loop ([xs nums] [acc '()])
    (cond
      [(or (null? xs) (null? (cdr xs)) (not (take-point!)))
       (string-join (reverse acc) " ")]
      [else (loop (cddr xs) (cons (format "~a,~a" (fmt-num (car xs)) (fmt-num (cadr xs))) acc))])))

;; Build a star / n-gon burst as a <polygon>.  Spike count is clamped.
(define (star-xexpr cx cy spikes outer inner fill)
  (define n (max 2 (min 100 (inexact->exact (floor spikes)))))
  (define pts
    (for/list ([k (in-range (* 2 n))] #:break (not (take-point!)))
      (define r (if (even? k) outer inner))
      (define ang (- (* k (/ pi n)) (/ pi 2)))
      (format "~a,~a" (fmt-num (+ cx (* r (cos ang)))) (fmt-num (+ cy (* r (sin ang)))))))
  `(polygon ((points ,(string-join pts " ")) (fill ,fill)) ""))

;; Regular n-gon (filled) centered at (cx,cy), first vertex pointing up.
(define (poly-xexpr cx cy sides r fill)
  (define n (max 3 (min 100 (inexact->exact (floor sides)))))
  (define pts
    (for/list ([k (in-range n)] #:break (not (take-point!)))
      (define ang (- (* k (/ (* 2 pi) n)) (/ pi 2)))
      (format "~a,~a" (fmt-num (+ cx (* r (cos ang)))) (fmt-num (+ cy (* r (sin ang)))))))
  `(polygon ((points ,(string-join pts " ")) (fill ,fill)) ""))

;; Parametric heart curve as a filled polygon, centered at (cx,cy).
(define (heart-xexpr cx cy size fill)
  (define s (/ size 17.0))
  (define pts
    (for/list ([k (in-range 0 360 6)] #:break (not (take-point!)))
      (define t (degrees->radians k))
      (define hx (* 16 (expt (sin t) 3)))
      (define hy (- (+ (* 13 (cos t)) (* -5 (cos (* 2 t))) (* -2 (cos (* 3 t))) (- (cos (* 4 t))))))
      (format "~a,~a" (fmt-num (+ cx (* s hx))) (fmt-num (+ cy (* s hy))))))
  `(polygon ((points ,(string-join pts " ")) (fill ,fill)) ""))

;; Stroked circular arc from angle a0 to a1 (degrees) as an SVG <path>.
(define (arc-xexpr cx cy r a0 a1 stroke width)
  (define rr (abs r))
  (define r0 (degrees->radians a0)) (define r1 (degrees->radians a1))
  (define x0 (+ cx (* rr (cos r0)))) (define y0 (+ cy (* rr (sin r0))))
  (define x1 (+ cx (* rr (cos r1)))) (define y1 (+ cy (* rr (sin r1))))
  (define large (if (> (abs (- a1 a0)) 180) 1 0))
  (define sweep (if (>= a1 a0) 1 0))
  `(path ((d ,(format "M ~a ~a A ~a ~a 0 ~a ~a ~a ~a"
                      (fmt-num x0) (fmt-num y0) (fmt-num rr) (fmt-num rr)
                      large sweep (fmt-num x1) (fmt-num y1)))
          (fill "none") (stroke ,stroke) (stroke-width ,(fmt-num width))
          (stroke-linecap "round"))
         ""))

;; Smooth open curve through a list of coordinate exprs, as a cubic-bezier
;; <path> (Catmull-Rom -> Bezier).  Point count is capped like polylines.
(define (curve-xexpr exprs env stroke width)
  (define nums (for/list ([e (in-list exprs)] [_ (in-range (* 2 MAX-POINTS))]
                          #:break (not (fuel-left? (current-ctx))))
                 (eval-num e env)))
  (define pts
    (let loop ([xs nums] [acc '()])
      (if (or (null? xs) (null? (cdr xs)) (not (take-point!)))
          (reverse acc)
          (loop (cddr xs) (cons (cons (car xs) (cadr xs)) acc)))))
  (cond
    [(< (length pts) 2) `(g () "")]
    [else
     (define vp (list->vector pts))
     (define n (vector-length vp))
     (define (px i) (car (vector-ref vp (max 0 (min (sub1 n) i)))))
     (define (py i) (cdr (vector-ref vp (max 0 (min (sub1 n) i)))))
     (define d (open-output-string))
     (fprintf d "M ~a ~a" (fmt-num (px 0)) (fmt-num (py 0)))
     (for ([i (in-range (sub1 n))])
       (define c1x (+ (px i) (/ (- (px (add1 i)) (px (sub1 i))) 6.0)))
       (define c1y (+ (py i) (/ (- (py (add1 i)) (py (sub1 i))) 6.0)))
       (define c2x (- (px (add1 i)) (/ (- (px (+ i 2)) (px i)) 6.0)))
       (define c2y (- (py (add1 i)) (/ (- (py (+ i 2)) (py i)) 6.0)))
       (fprintf d " C ~a ~a ~a ~a ~a ~a" (fmt-num c1x) (fmt-num c1y)
                (fmt-num c2x) (fmt-num c2y) (fmt-num (px (add1 i))) (fmt-num (py (add1 i)))))
     `(path ((d ,(get-output-string d)) (fill "none") (stroke ,stroke)
             (stroke-width ,(fmt-num width)) (stroke-linecap "round") (stroke-linejoin "round")) "")]))

;; Archimedean spiral from radius r0 to r1 over `turns` turns, as a stroked path.
(define (spiral-xexpr cx cy turns r0 r1 stroke width)
  (define tt (max 0.1 (min 30 (abs turns))))
  (define steps (max 2 (min 1200 (inexact->exact (floor (* tt 40))))))
  (define d (open-output-string))
  (for ([k (in-range (add1 steps))] #:break (not (take-point!)))
    (define f (/ k (exact->inexact steps)))
    (define ang (* f tt 2 pi))
    (define r (+ r0 (* (- r1 r0) f)))
    (define x (+ cx (* r (cos ang)))) (define y (+ cy (* r (sin ang))))
    (fprintf d "~a~a ~a" (if (= k 0) "M " " L ") (fmt-num x) (fmt-num y)))
  `(path ((d ,(get-output-string d)) (fill "none") (stroke ,stroke)
          (stroke-width ,(fmt-num width)) (stroke-linecap "round")) ""))

;; Filled pie slice (sector) from angle a0 to a1 (degrees).
(define (sector-xexpr cx cy r a0 a1 fill)
  (define rr (abs r))
  (define r0 (degrees->radians a0)) (define r1 (degrees->radians a1))
  (define x0 (+ cx (* rr (cos r0)))) (define y0 (+ cy (* rr (sin r0))))
  (define x1 (+ cx (* rr (cos r1)))) (define y1 (+ cy (* rr (sin r1))))
  (define large (if (> (abs (- a1 a0)) 180) 1 0))
  (define sweep (if (>= a1 a0) 1 0))
  `(path ((d ,(format "M ~a ~a L ~a ~a A ~a ~a 0 ~a ~a ~a ~a Z"
                      (fmt-num cx) (fmt-num cy) (fmt-num x0) (fmt-num y0)
                      (fmt-num rr) (fmt-num rr) large sweep (fmt-num x1) (fmt-num y1)))
          (fill ,fill)) ""))

;; Build a gradient <defs> node (linear or radial) with evenly spaced stops
;; from a list of color strings, and return its url(#id) reference.
(define (gradient-url kind colors env [extra '()])
  (define stops
    (for/list ([c (in-list colors)] [k (in-naturals)])
      (define off (if (= (length colors) 1) 0
                      (exact->inexact (/ k (sub1 (length colors))))))
      `(stop ((offset ,(string-append (~r (* 100 off) #:precision 1) "%")) (stop-color ,(eval-color c env))) "")))
  ;; Dedup identical gradients (resolved stops + kind + extra), so a loop that
  ;; fills thousands of shapes with the same gradient emits one <defs> entry.
  (define cache (rctx-defcache (current-ctx)))
  (define key (list kind stops extra))
  (or (hash-ref cache key #f)
      (let ([url (format "url(#~a)"
                         (add-def!
                          (lambda (gid)
                            (if (eq? kind 'linear)
                                `(linearGradient ((id ,gid) ,@extra) ,@stops)
                                `(radialGradient ((id ,gid) ,@extra) ,@stops)))))])
        (hash-set! cache key url)
        url)))

;; Register an SVG <filter> (wide region so blurs/glows don't clip) built from
;; the given primitive nodes, and return its url(#id) reference.  Identical
;; filters are deduplicated, so a loop that glows thousands of shapes emits one
;; <filter>, not thousands.
(define (filter-url . prims)
  (define cache (rctx-defcache (current-ctx)))
  (or (hash-ref cache prims #f)
      (let ([url (format "url(#~a)"
                         (add-def!
                          (lambda (fid)
                            `(filter ((id ,fid) (x "-50%") (y "-50%") (width "200%") (height "200%")) ,@prims))))])
        (hash-set! cache prims url)
        url)))

(define (blur-filter amount)
  (filter-url `(feGaussianBlur ((in "SourceGraphic") (stdDeviation ,(fmt-num amount))) "")))

(define (glow-filter color amount)
  (filter-url
   `(feColorMatrix ((in "SourceAlpha") (type "matrix")
                    (values "0 0 0 0 1  0 0 0 0 1  0 0 0 0 1  0 0 0 1 0") (result "a")) "")
   `(feGaussianBlur ((in "a") (stdDeviation ,(fmt-num amount)) (result "b")) "")
   `(feFlood ((flood-color ,color) (result "c")) "")
   `(feComposite ((in "c") (in2 "b") (operator "in") (result "glow")) "")
   `(feMerge () (feMergeNode ((in "glow")) "") (feMergeNode ((in "SourceGraphic")) ""))))

(define (shadow-filter dx dy amount color)
  (filter-url
   `(feDropShadow ((dx ,(fmt-num dx)) (dy ,(fmt-num dy)) (stdDeviation ,(fmt-num amount))
                   (flood-color ,color) (flood-opacity "0.6")) "")))

;; Interpret one command into a list of SVG xexprs.  `env` carries constants /
;; the loop index / locals, `depth` bounds nesting, `ctx` bounds total output.
;; Every path is guarded so malformed or hostile input degrades to a small
;; error node instead of an exception/hang.
(define (interpret cmd env ctx depth)
  (burn! 1)
  (cond
    [(not (alive? ctx)) '()]
    [(> depth MAX-DEPTH) '()]
    [else
     ;; A raised error or an invalid command still emits a node, so it must
     ;; cost element budget — otherwise a flood of them bypasses every cap.
     (with-handlers ([exn:fail? (lambda (e) (note-error! ctx "Eroare interpretare" (exn-message e) 24))])
       (define (n v) (fmt-num (eval-num v env)))
       (define (col c) (eval-color c env))
       ;; Run a body of commands in env e at depth d, honoring the live budget.
       (define (run body e d)
         (apply append (for/list ([b (in-list body)] #:break (not (alive? ctx)))
                         (interpret b e ctx d))))
       ;; Emit a <g transform=...> wrapper around a body (shared by the
       ;; transform commands); costs one element for the group itself.
       (define (wrap-g transform body)
         (spend! ctx)
         (list `(g ((transform ,transform)) ,@(run body env (add1 depth)))))
       (match cmd
         [(list 'circle cx cy r c)
          (spend! ctx)
          (list `(circle ((cx ,(n cx)) (cy ,(n cy)) (r ,(n r)) (fill ,(col c))) ""))]
         [(list 'rect x y w h c)
          (spend! ctx)
          (list `(rect ((x ,(n x)) (y ,(n y)) (width ,(n w)) (height ,(n h)) (fill ,(col c))) ""))]
         [(list 'ellipse cx cy rx ry c)
          (spend! ctx)
          (list `(ellipse ((cx ,(n cx)) (cy ,(n cy)) (rx ,(n rx)) (ry ,(n ry)) (fill ,(col c))) ""))]
         [(list 'line x1 y1 x2 y2 c w)
          (spend! ctx)
          (list `(line ((x1 ,(n x1)) (y1 ,(n y1)) (x2 ,(n x2)) (y2 ,(n y2))
                        (stroke ,(col c)) (stroke-width ,(n w))) ""))]
         [(list 'text x y size c (? string? s))
          (spend! ctx)
          (list `(text ((x ,(n x)) (y ,(n y)) (font-size ,(n size))
                        (font-family "system-ui, sans-serif") (fill ,(col c)))
                       ,(clip-text s)))]
         [(list 'bg c)
          (spend! ctx)
          (list `(rect ((x "0") (y "0") (width "600") (height "400") (fill ,(col c))) ""))]
         [(list 'polygon c pts ...)
          (spend! ctx)
          (list `(polygon ((points ,(points->str pts env)) (fill ,(col c))) ""))]
         [(list 'polyline c w pts ...)
          (spend! ctx)
          (list `(polyline ((points ,(points->str pts env)) (fill "none")
                            (stroke ,(col c)) (stroke-width ,(n w))) ""))]
         [(list 'star cx cy spikes outer inner c)
          (spend! ctx)
          (list (star-xexpr (eval-num cx env) (eval-num cy env) (eval-num spikes env)
                            (eval-num outer env) (eval-num inner env) (col c)))]
         [(list 'triangle x1 y1 x2 y2 x3 y3 c)
          (spend! ctx)
          (list `(polygon ((points ,(points->str (list x1 y1 x2 y2 x3 y3) env)) (fill ,(col c))) ""))]
         [(list 'poly cx cy sides r c)
          (spend! ctx)
          (list (poly-xexpr (eval-num cx env) (eval-num cy env) (eval-num sides env)
                            (eval-num r env) (col c)))]
         [(list 'heart cx cy size c)
          (spend! ctx)
          (list (heart-xexpr (eval-num cx env) (eval-num cy env) (eval-num size env) (col c)))]
         [(list 'ring cx cy r c w)
          (spend! ctx)
          (list `(circle ((cx ,(n cx)) (cy ,(n cy)) (r ,(n r)) (fill "none")
                          (stroke ,(col c)) (stroke-width ,(n w))) ""))]
         [(list 'arc cx cy r a0 a1 c w)
          (spend! ctx)
          (list (arc-xexpr (eval-num cx env) (eval-num cy env) (eval-num r env)
                           (eval-num a0 env) (eval-num a1 env) (col c) (eval-num w env)))]
         [(list 'sector cx cy r a0 a1 c)
          (spend! ctx)
          (list (sector-xexpr (eval-num cx env) (eval-num cy env) (eval-num r env)
                              (eval-num a0 env) (eval-num a1 env) (col c)))]
         [(list 'spiral cx cy turns r0 r1 c w)
          (spend! ctx)
          (list (spiral-xexpr (eval-num cx env) (eval-num cy env) (eval-num turns env)
                              (eval-num r0 env) (eval-num r1 env) (col c) (eval-num w env)))]
         [(list* 'curve c w pts)
          (spend! ctx)
          (list (curve-xexpr pts env (col c) (eval-num w env)))]

         ;; --- SVG filter effects (registered in <defs>, no JS) --------------
         [(list* 'blur amount body)
          (spend! ctx)
          (define f (blur-filter (max 0 (min 40 (eval-num amount env)))))
          (list `(g ((filter ,f)) ,@(run body env (add1 depth))))]
         [(list* 'glow gc body)
          (spend! ctx)
          (define f (glow-filter (col gc) 4))
          (list `(g ((filter ,f)) ,@(run body env (add1 depth))))]
         [(list* 'shadow dx dy amount sc body)
          (spend! ctx)
          (define f (shadow-filter (eval-num dx env) (eval-num dy env)
                                   (max 0 (min 40 (eval-num amount env))) (col sc)))
          (list `(g ((filter ,f)) ,@(run body env (add1 depth))))]

         ;; --- gradients (register a <defs> entry + fill the canvas) ----------
         [(list* 'linear-bg angle colors)
          (spend! ctx)
          (define cs (if (null? colors) (list "#000" "#fff") colors))
          (define url (gradient-url 'linear cs env
                                    (list `(gradientTransform
                                            ,(format "rotate(~a 0.5 0.5)" (fmt-num (eval-num angle env)))))))
          (list `(rect ((x "0") (y "0") (width "600") (height "400") (fill ,url)) ""))]
         [(list* 'radial-bg colors)
          (spend! ctx)
          (define cs (if (null? colors) (list "#fff" "#000") colors))
          (list `(rect ((x "0") (y "0") (width "600") (height "400")
                        (fill ,(gradient-url 'radial cs env))) ""))]

         ;; --- transforms / grouping -----------------------------------------
         [(list* 'group body)             (wrap-g "translate(0,0)" body)]
         [(list* 'rotate deg cx cy body)  (wrap-g (format "rotate(~a ~a ~a)" (n deg) (n cx) (n cy)) body)]
         [(list* 'translate dx dy body)   (wrap-g (format "translate(~a ~a)" (n dx) (n dy)) body)]
         [(list* 'scale sx sy body)       (wrap-g (format "scale(~a ~a)" (n sx) (n sy)) body)]
         [(list* 'opacity a body)
          (spend! ctx)
          (list `(g ((opacity ,(clamp-unit (eval-num a env)))) ,@(run body env (add1 depth))))]
         ;; Outline every shape in the body (shapes inherit stroke from the <g>
         ;; unless they set their own).
         [(list* 'stroke c w body)
          (spend! ctx)
          (list `(g ((stroke ,(col c)) (stroke-width ,(n w)) (stroke-linejoin "round"))
                    ,@(run body env (add1 depth))))]
         ;; Dashed strokes: on/off dash lengths (implies a stroke; pair with
         ;; `stroke` for color, or on already-stroked shapes like line/arc).
         [(list* 'dash on off body)
          (spend! ctx)
          (list `(g ((stroke-dasharray ,(format "~a,~a" (n on) (n off))))
                    ,@(run body env (add1 depth))))]

         ;; --- SVG-native animation (works in the page and the downloaded file)
         [(list* 'spin cx cy dur body)
          (spend! ctx)
          (define d (max 0.2 (min 120 (eval-num dur env))))
          (define cxs (n cx)) (define cys (n cy))
          (list `(g () (animateTransform ((attributeName "transform") (attributeType "XML")
                          (type "rotate") (from ,(format "0 ~a ~a" cxs cys))
                          (to ,(format "360 ~a ~a" cxs cys))
                          (dur ,(format "~as" (~r d #:precision 2))) (repeatCount "indefinite")) "")
                   ,@(run body env (add1 depth))))]
         [(list* 'pulse dur body)
          (spend! ctx)
          (define d (max 0.2 (min 120 (eval-num dur env))))
          (list `(g () (animate ((attributeName "opacity") (values "1;0.35;1")
                          (dur ,(format "~as" (~r d #:precision 2))) (repeatCount "indefinite")) "")
                   ,@(run body env (add1 depth))))]

         ;; --- reproducible randomness ---------------------------------------
         [(list 'seed s)
          (random-seed (max 1 (modulo (abs (inexact->exact (floor (eval-num s env)))) 2147483646)))
          '()]

         [(cons 'let (cons bindings body))
          (define env*
            (if (list? bindings)
                (for/fold ([e env]) ([bnd (in-list bindings)])
                  (match bnd
                    [(list (? symbol? name) vexpr) (hash-set e name (eval-num vexpr env))]
                    [_ e]))
                env))
          (apply append (for/list ([b (in-list body)]) (interpret b env* ctx (add1 depth))))]
         [(list 'repeat count body ...)
          (spend! ctx)
          (define reps (min MAX-REPEAT (max 0 (inexact->exact (floor (eval-num count env))))))
          (apply append
                 (for/list ([i (in-range reps)] #:break (not (alive? ctx)))
                   (burn! 1) ; charge every iteration so empty-body loops are bounded
                   (define env* (hash-set env 'i i))
                   (apply append
                          (for/list ([b (in-list body)]) (interpret b env* ctx (add1 depth))))))]
         ;; (for name start end [step] body...): bind `name` across a range.
         ;; A numeric literal right after `end` is the step; otherwise step is
         ;; +1/-1 toward `end`.  Total iterations are bounded like `repeat`.
         [(list* 'for (? symbol? name) start-e end-e more)
          (spend! ctx)
          (define a (eval-num start-e env)) (define b (eval-num end-e env))
          (define step-given (and (pair? more) (number? (car more))))
          (define body (if step-given (cdr more) more))
          (define raw (if step-given (car more) (if (<= a b) 1 -1)))
          (define st (if (zero? raw) (if (<= a b) 1 -1) raw))
          (define cnt (min MAX-REPEAT (max 0 (add1 (inexact->exact (floor (/ (abs (- b a)) (max 1e-6 (abs st)))))))))
          (apply append
                 (for/list ([k (in-range cnt)] #:break (not (alive? ctx)))
                   (burn! 1)
                   (define env* (hash-set env name (+ a (* k st))))
                   (run body env* (add1 depth))))]
         ;; (grid cols rows body...): nested loop exposing gx (col), gy (row)
         ;; and gi (flat index).
         [(list* 'grid cols-e rows-e body)
          (spend! ctx)
          (define cols (max 0 (min 200 (inexact->exact (floor (eval-num cols-e env))))))
          (define rows (max 0 (min 200 (inexact->exact (floor (eval-num rows-e env))))))
          (define total (min MAX-REPEAT (* cols rows)))
          (apply append
                 (for/list ([gi (in-range total)] #:break (not (alive? ctx)))
                   (burn! 1)
                   (define env* (hash-set (hash-set (hash-set env 'gx (modulo gi cols))
                                                    'gy (quotient gi cols)) 'gi gi))
                   (run body env* (add1 depth))))]
         [_ (note-error! ctx "Comanda invalida" (short-str cmd) 40)]))]))

;; ---------------------------------------------------------------------------
;; Parsing.  We read S-expressions with a hardened reader:
;;   * read-accept-graph  #f  -> no #0=(1 . #0#) cyclic structures (would hang
;;                               downstream traversal/printing);
;;   * read-accept-reader #f  -> no #lang / #reader (no code loading at read);
;;   * read-accept-compiled #f;
;;   * input length is capped before we ever hand bytes to `read`.
;; ---------------------------------------------------------------------------
(define (clip-code text)
  (cond [(not (string? text)) ""]
        [(> (string-length text) MAX-CODE-LENGTH) (substring text 0 MAX-CODE-LENGTH)]
        [else text]))

(define (safe-read-all text)
  (parameterize ([read-accept-graph #f]
                 [read-accept-reader #f]
                 [read-accept-compiled #f]
                 [read-accept-quasiquote #f]
                 [read-decimal-as-inexact #t])
    (with-handlers ([exn:fail? (lambda (_) '())])
      (read (open-input-string (string-append "(" (clip-code text) "\n)"))))))

(define (parse-to-svg text)
  (define forms (safe-read-all text))
  (define ctx (make-rctx))
  ;; Two layers of defense:
  ;;   1. The in-interpreter fuel/budget/point caps (fast, bound the common case).
  ;;   2. call-with-limits — a hard wall-clock + memory ceiling run in a child
  ;;      custodian, so even an unforeseen pathological path is killed and
  ;;      confined to THIS request instead of OOM-ing the shared process.
  (define-values (elements limited?)
    (with-handlers ([exn:fail:resource? (lambda (_) (values '() #t))]
                    [exn:fail?          (lambda (_) (values '() #t))])
      (call-with-limits RENDER-TIME-SEC RENDER-MEM-MB
        (lambda ()
          ;; A fresh PRG per render so (seed N) is reproducible and isolated
          ;; between requests.
          (parameterize ([current-ctx ctx]
                         [current-pseudo-random-generator (make-pseudo-random-generator)])
            (define els
              (if (list? forms)
                  (apply append
                         (for/list ([c (in-list forms)] #:break (not (alive? ctx)))
                           (interpret c BASE-ENV ctx 0)))
                  '()))
            (values els #f))))))
  ;; Gradients registered during interpretation go into a <defs> block first.
  (define defs (rctx-defs ctx))
  (define defs-node (if (null? defs) '() (list `(defs () ,@(reverse defs)))))
  (define notice
    (if (or limited? (<= (rctx-budget ctx) 0) (<= (rctx-fuel ctx) 0) (<= (rctx-points ctx) 0))
        (list `(text ((x "12") (y "392") (fill "#ffb86c") (font-family "monospace") (font-size "12"))
                     "… limita de complexitate atinsa (output trunchiat)"))
        '()))
  ;; viewBox lets the canvas scale to any container width while keeping the
  ;; 600x400 coordinate system; explicit width/height keep the downloaded file
  ;; usable standalone.
  `(svg ((xmlns "http://www.w3.org/2000/svg")
         (viewBox "0 0 600 400")
         (width "600") (height "400")
         (preserveAspectRatio "xMidYMid meet")
         (style "background:#000;border-radius:12px;display:block;width:100%;height:auto;"))
        ,@defs-node ,@elements ,@notice))

;; ---------------------------------------------------------------------------
;; Image -> DSL.  Bounded on every axis: output resolution is capped (so a
;; 1xN "tall" image can't explode target-h into a giant loop) and the number
;; of emitted primitives is hard-limited.
;; ---------------------------------------------------------------------------
(define IMG-TARGET-W 50)
(define IMG-MAX-H    50)
(define IMG-MAX-DOTS 3000)

(define (image->dsl bytes-data)
  (with-handlers ([exn:fail? (lambda (e) (string-append ";; Eroare procesare imagine: " (exn-message e)))])
    (define bmp (make-object bitmap% (open-input-bytes bytes-data)))
    (if (not (send bmp ok?))
        ";; Eroare: fisierul nu este o imagine valida (JPG/PNG)."
        (let* ([w (max 1 (send bmp get-width))]
               [h (max 1 (send bmp get-height))]
               [target-w IMG-TARGET-W]
               [target-h (max 1 (min IMG-MAX-H (inexact->exact (round (* target-w (/ h w))))))]
               [scaled (make-object bitmap% target-w target-h)]
               [dc (make-object bitmap-dc% scaled)])
          (send dc set-smoothing 'smoothed)
          (send dc set-scale (/ target-w w) (/ target-h h))
          (send dc draw-bitmap bmp 0 0)
          (define px (make-bytes (* target-w target-h 4)))
          (send scaled get-argb-pixels 0 0 target-w target-h px)
          (define out (open-output-string))
          (fprintf out ";; Imagine convertita automat in cod DSL (rezolutie ~ax~a)\n" target-w target-h)
          (define dots 0)
          (for* ([y (in-range target-h)] [x (in-range target-w)] #:break (>= dots IMG-MAX-DOTS))
            (define idx (* 4 (+ (* y target-w) x)))
            (define a (bytes-ref px idx))
            (when (> a 10)
              (set! dots (add1 dots))
              (fprintf out "(circle ~a ~a 5 \"rgb(~a,~a,~a)\")\n"
                       (inexact->exact (round (* x (/ 600 target-w))))
                       (inexact->exact (round (* y (/ 400 target-h))))
                       (bytes-ref px (+ idx 1)) (bytes-ref px (+ idx 2)) (bytes-ref px (+ idx 3)))))
          (get-output-string out)))))

;; ---------------------------------------------------------------------------
;; HTTP
;; ---------------------------------------------------------------------------

;; Decode bytes without ever throwing on invalid UTF-8 (would 500 the request).
(define (bytes->string* bs)
  (if (bytes? bs) (bytes->string/utf-8 bs #\uFFFD) ""))

(define (req-path req)
  (string-join (map path/param-path (url-path (request-uri req))) "/"))

;; Decode a shared program from the ?c= permalink: standard base64 of the
;; UTF-8 source.  Bounded and failure-tolerant (bad input -> #f).
(define MAX-SHARE-CHARS 12000)
(define (decode-share s)
  (with-handlers ([exn:fail? (lambda (_) #f)])
    (and (string? s) (non-empty-string? s) (<= (string-length s) MAX-SHARE-CHARS)
         (let ([txt (bytes->string* (base64-decode (string->bytes/utf-8 s)))])
           (and (non-empty-string? txt) (clip-code txt))))))

;; Encode code into a ?c= permalink value (base64 + percent-encoding of +,/,=).
(define (encode-share code)
  (define b (bytes->string/utf-8 (base64-encode (string->bytes/utf-8 code) #"")))
  (string-replace (string-replace (string-replace b "+" "%2B") "/" "%2F") "=" "%3D"))

;; Client IP as set by nginx (X-Real-IP); used only for per-IP save throttling.
(define (req-ip req)
  (with-handlers ([exn:fail? (lambda (_) "?")])
    (define h (headers-assq* #"X-Real-IP" (request-headers/raw req)))
    (if h (bytes->string* (header-value h)) "?")))

;; ---------------------------------------------------------------------------
;; Social share image (Open Graph / Twitter).  Rendered once with racket/draw
;; to a real PNG — SVG OG images are poorly supported by scrapers — and cached.
;; ---------------------------------------------------------------------------
(define og-png-cache #f)
(define (og-png-bytes)
  (or og-png-cache
      (let ()
        (define W 1200) (define H 630)
        (define bmp (make-object bitmap% W H))
        (define dc (make-object bitmap-dc% bmp))
        (send dc set-smoothing 'smoothed)
        (send dc set-pen "black" 0 'transparent)
        ;; vertical gradient background
        (for ([y (in-range 0 H 2)])
          (define t (/ y (exact->inexact H)))
          (send dc set-brush (make-object color%
                               (inexact->exact (round (+ 11 (* t 15))))
                               (inexact->exact (round (+ 13 (* t 6))))
                               (inexact->exact (round (+ 20 (* t 28))))) 'solid)
          (send dc draw-rectangle 0 y W 2))
        ;; procedural swirl (the signature default art), upper-right
        (for ([i (in-range 230)])
          (define a (* i 0.33)) (define r (* i 1.95))
          (define x (+ 820 (* r (cos a)))) (define y (+ 250 (* r (sin a))))
          (match-define (list cr cg cb) (hsl->rgb (* i 4) 85 62))
          (send dc set-brush (make-object color% cr cg cb) 'solid)
          (send dc draw-ellipse (- x 8) (- y 8) 16 16))
        ;; dark scrim over the lower band so the title stays legible over art
        (send dc set-alpha 0.62)
        (send dc set-brush (make-object color% 8 9 16) 'solid)
        (send dc draw-rectangle 0 380 W 250)
        (send dc set-alpha 1.0)
        ;; title + tagline
        (send dc set-text-foreground (make-object color% 231 233 243))
        (send dc set-font (make-object font% 58 'default 'normal 'bold))
        (send dc draw-text "Procedural Canvas DSL" 70 440)
        (send dc set-text-foreground (make-object color% 154 163 189))
        (send dc set-font (make-object font% 29 'default 'normal 'normal))
        (send dc draw-text "Scrie cod Lisp, obtii arta SVG · Racket + web-server" 72 522)
        (define out (open-output-bytes))
        (send bmp save-file out 'png)
        (set! og-png-cache (get-output-bytes out))
        og-png-cache)))

;; Count emitted element nodes in a rendered SVG (for the live status line).
(define (count-svg-nodes x)
  (cond [(and (pair? x) (symbol? (car x)))
         (for/fold ([acc 1]) ([c (in-list (cddr x))]) (+ acc (count-svg-nodes c)))]
        [(list? x) (for/fold ([acc 0]) ([c (in-list x)]) (+ acc (count-svg-nodes c)))]
        [else 0]))

;; ---------------------------------------------------------------------------
;; Community gallery — a public, unauthenticated store of saved creations, so
;; every write is treated as hostile.  Bounded on every axis: a ring buffer
;; caps row count (so disk is bounded), per-entry size caps, a per-IP cooldown,
;; and a minimum element count so blank/garbage saves are rejected.  All SQL is
;; parameterized; thumbnails are served as inert SVG images, never inlined.
;; ---------------------------------------------------------------------------
(define MAX-GALLERY     150)              ; rows kept (oldest evicted beyond this)
(define GALLERY-PAGE    24)               ; cards per gallery page
(define MAX-TITLE       60)               ; title chars
(define MAX-SAVE-CODE   4000)             ; code chars accepted for a save
(define MAX-SAVE-SVG    (* 160 1024))     ; stored thumbnail bytes
(define MIN-SAVE-ELEMS  3)                ; reject near-empty / all-error art
(define SAVE-COOLDOWN   12000)            ; ms between saves per client IP
(define DB-PATH (or (getenv "GALLERY_DB") "gallery.sqlite"))

(define gallery-lock (make-semaphore 1))
(define gallery-conn #f)
(define ip-last (make-hash))              ; ip -> last-save epoch ms (guarded by lock)

;; Lazily open the connection and ensure the schema; returns #f if the DB is
;; unavailable (feature degrades off rather than crashing the app).
(define (gallery-db)
  (or gallery-conn
      (with-handlers ([exn:fail? (lambda (_) #f)])
        (define c (sqlite3-connect #:database DB-PATH #:mode 'create))
        (query-exec c (string-append
                       "CREATE TABLE IF NOT EXISTS creations("
                       "id INTEGER PRIMARY KEY AUTOINCREMENT,"
                       "title TEXT NOT NULL, code TEXT NOT NULL, svg TEXT NOT NULL,"
                       "created INTEGER NOT NULL, ip TEXT)"))
        ;; migration: add the likes column (ignored if it already exists) and a
        ;; dedup table so each IP can like a creation only once.
        (with-handlers ([exn:fail? void])
          (query-exec c "ALTER TABLE creations ADD COLUMN likes INTEGER NOT NULL DEFAULT 0"))
        (query-exec c (string-append
                       "CREATE TABLE IF NOT EXISTS likes_log("
                       "creation INTEGER NOT NULL, ip TEXT NOT NULL,"
                       "PRIMARY KEY(creation, ip))"))
        (set! gallery-conn c)
        c)))

(define (sanitize-title s)
  (define t (string-normalize-spaces (regexp-replace* #px"[\u0000-\u001f]" (if (string? s) s "") " ")))
  (define tt (string-trim t))
  (cond [(= (string-length tt) 0) "fara titlu"]
        [(> (string-length tt) MAX-TITLE) (substring tt 0 MAX-TITLE)]
        [else tt]))

;; Attempt to save a creation.  Returns (values ok? message).  Everything runs
;; under the lock: the cooldown table, the render and the DB writes.
(define (gallery-save! title code ip)
  (call-with-semaphore gallery-lock
    (lambda ()
      (define now (current-inexact-milliseconds))
      (define c (gallery-db))
      (cond
        [(not c) (values #f "Galeria este indisponibila momentan.")]
        [(not (and (string? code) (non-empty-string? (string-trim code))))
         (values #f "Nu e nimic de salvat.")]
        [(> (string-length code) MAX-SAVE-CODE)
         (values #f (format "Cod prea lung pentru galerie (max ~a caractere)." MAX-SAVE-CODE))]
        [(let ([last (hash-ref ip-last ip #f)]) (and last (< (- now last) SAVE-COOLDOWN)))
         (values #f "Prea repede — asteapta cateva secunde si incearca din nou.")]
        [else
         (define svg-x (parse-to-svg code))
         (define svg (xexpr->string svg-x))
         (cond
           [(< (count-svg-nodes svg-x) MIN-SAVE-ELEMS)
            (values #f "Creatia pare goala — randeaza ceva vizibil intai.")]
           [(> (string-length svg) MAX-SAVE-SVG)
            (values #f "Creatia e prea complexa pentru o miniatura din galerie.")]
           [else
            (with-handlers ([exn:fail? (lambda (_) (values #f "Nu am putut salva."))])
              (query-exec c "INSERT INTO creations(title,code,svg,created,ip) VALUES (?,?,?,?,?)"
                          (sanitize-title title) code svg (inexact->exact (floor now)) (or ip ""))
              ;; ring buffer: evict anything older than the newest MAX-GALLERY
              (query-exec c (string-append
                             "DELETE FROM creations WHERE id NOT IN "
                             "(SELECT id FROM creations ORDER BY id DESC LIMIT ?)") MAX-GALLERY)
              ;; drop likes for evicted creations so likes_log stays bounded
              (query-exec c "DELETE FROM likes_log WHERE creation NOT IN (SELECT id FROM creations)")
              (hash-set! ip-last ip now)
              (values #t "Salvat in galerie!"))])]))))

;; Creations as (id, title, code, likes).  sort 'popular orders by likes then
;; recency and ignores `before`; otherwise newest-first with keyset pagination.
(define (gallery-list before [sort 'recent])
  (define c (gallery-db))
  (cond
    [(not c) '()]
    [else
     (with-handlers ([exn:fail? (lambda (_) '())])
       (call-with-semaphore gallery-lock
         (lambda ()
           (cond
             [(eq? sort 'popular)
              (query-rows c "SELECT id,title,code,likes FROM creations ORDER BY likes DESC, id DESC LIMIT ?" GALLERY-PAGE)]
             [(and before (exact-integer? before))
              (query-rows c "SELECT id,title,code,likes FROM creations WHERE id<? ORDER BY id DESC LIMIT ?" before GALLERY-PAGE)]
             [else
              (query-rows c "SELECT id,title,code,likes FROM creations ORDER BY id DESC LIMIT ?" GALLERY-PAGE)]))))]))

;; Stored thumbnail SVG for an id, or #f.
(define (gallery-svg id)
  (define c (gallery-db))
  (and c (exact-integer? id)
       (with-handlers ([exn:fail? (lambda (_) #f)])
         (call-with-semaphore gallery-lock
           (lambda ()
             (define r (query-maybe-value c "SELECT svg FROM creations WHERE id=?" id))
             (and (string? r) r))))))

;; Like a creation once per IP.  Returns the new like count, or #f if the
;; creation is gone, the IP already liked it, or the DB is unavailable.
(define (gallery-like! id ip)
  (define c (gallery-db))
  (and c (exact-integer? id)
       (with-handlers ([exn:fail? (lambda (_) #f)])
         (call-with-semaphore gallery-lock
           (lambda ()
             (cond
               [(not (query-maybe-value c "SELECT 1 FROM creations WHERE id=?" id)) #f]
               [(query-maybe-value c "SELECT 1 FROM likes_log WHERE creation=? AND ip=?" id (or ip "")) #f]
               [else
                (query-exec c "INSERT INTO likes_log(creation,ip) VALUES (?,?)" id (or ip ""))
                (query-exec c "UPDATE creations SET likes=likes+1 WHERE id=?" id)
                (query-value c "SELECT likes FROM creations WHERE id=?" id)]))))))

(define DEFAULT-CODE
  (string-append
   ";; (i) = indexul buclei. Incearca: noise, mix, gradient, spin, seed.\n"
   "(linear-bg 60 \"#0b0f1a\" \"#1a1030\" \"#0b0f1a\")\n\n"
   ";; Un vartej care se roteste (animatie SVG nativa)\n"
   "(spin 300 200 32\n"
   "  (repeat 90\n"
   "    (circle (+ 300 (* (* i 2.2) (cos (* i 0.35))))\n"
   "            (+ 200 (* (* i 2.2) (sin (* i 0.35))))\n"
   "            6\n"
   "            (mix \"#8be9fd\" \"#ff79c6\" (noise i 2)))))\n\n"
   ";; O stea care pulseaza in centru\n"
   "(pulse 3 (star 300 200 5 40 16 \"#f1fa8c\"))"))

;; ---------------------------------------------------------------------------
;; UI: mobile-first responsive page.  The app is server-rendered and fully
;; usable without JavaScript (examples are plain POST forms); JS only adds the
;; copy-to-clipboard convenience and the chosen-file name.
;; ---------------------------------------------------------------------------
(define PAGE-CSS "
:root{--bg:#0b0d14;--bg2:#0f121b;--panel:#161a26;--panel2:#1b2030;--border:#272d40;
--border2:#333b52;--text:#e7e9f3;--muted:#9aa3bd;--purple:#bd93f9;--pink:#ff79c6;
--cyan:#8be9fd;--green:#50fa7b;--yellow:#f1fa8c;--radius:14px;--btn-text:#12131a;
--glow1:#1a1030;--glow2:#08202b}
/* Light shell (editor, canvas and code chips intentionally stay dark). */
:root[data-theme=light]{--bg:#eef1f8;--bg2:#e6ebf5;--panel:#ffffff;--panel2:#f2f5fc;
--border:#dbe1f0;--border2:#c4cce2;--text:#141a2e;--muted:#55607c;--purple:#7c3aed;
--pink:#d6287e;--cyan:#0e7490;--green:#0a7f53;--yellow:#9a7b1f;--btn-text:#ffffff;
--glow1:#e4d7ff;--glow2:#d4ecff}
*{box-sizing:border-box}html{-webkit-text-size-adjust:100%;scroll-behavior:smooth}
body{margin:0;font-family:system-ui,-apple-system,Roboto,Arial,sans-serif;color:var(--text);
line-height:1.55;min-height:100vh;background:
radial-gradient(1100px 560px at 82% -12%,var(--glow1) 0,transparent 60%),
radial-gradient(950px 480px at -8% 8%,var(--glow2) 0,transparent 55%),var(--bg)}
a{color:var(--cyan);text-decoration:none}a:hover{text-decoration:underline}
.wrap{max-width:1200px;margin:0 auto;padding:clamp(1rem,3.5vw,2.25rem)}
.hero{text-align:center;margin-bottom:1.4rem}
.hero h1{font-size:clamp(1.6rem,5vw,2.5rem);margin:.25rem 0;font-weight:800;
background:linear-gradient(90deg,var(--purple),var(--pink),var(--cyan));
-webkit-background-clip:text;background-clip:text;color:transparent}
.hero p{color:var(--muted);margin:.25rem auto 0;max-width:46ch;font-size:clamp(.92rem,2.5vw,1.05rem)}
.badge{display:inline-block;font-size:.7rem;letter-spacing:.09em;text-transform:uppercase;
color:var(--purple);border:1px solid var(--border2);border-radius:999px;padding:.2rem .7rem;margin-bottom:.5rem}
.grid{display:grid;gap:1.15rem;grid-template-columns:1fr}
@media(min-width:920px){.grid{grid-template-columns:minmax(0,1fr) minmax(0,1fr);align-items:start}
.grid>.panel:nth-child(2){position:sticky;top:1rem}}
.panel{background:linear-gradient(180deg,var(--panel),var(--bg2));border:1px solid var(--border);
border-radius:var(--radius);padding:clamp(.9rem,2.5vw,1.25rem);box-shadow:0 12px 30px rgba(0,0,0,.35)}
.panel h2{font-size:.82rem;margin:0 0 .7rem;color:var(--muted);text-transform:uppercase;letter-spacing:.07em}
textarea{width:100%;min-height:340px;resize:vertical;background:#0b0e17;color:#f5f6ff;
border:1px solid var(--border);border-radius:10px;padding:1rem;tab-size:2;
font:15px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
textarea:focus,input:focus,button:focus-visible,.btn:focus-visible{outline:2px solid var(--purple);outline-offset:2px}
/* --- pro editor: gutter + syntax-highlight overlay under the textarea --- */
.editor-wrap{position:relative;min-height:340px}
.editor-wrap textarea,.hl{box-sizing:border-box;width:100%;min-height:340px;margin:0;
border:1px solid var(--border);border-radius:10px;padding:1rem;tab-size:2;
font:15px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
white-space:pre;overflow:auto;letter-spacing:normal}
.hl{position:absolute;inset:0;z-index:1;background:#0b0e17;color:#8089a8;
pointer-events:none;overflow:hidden;display:none}
.editor-wrap textarea{position:relative;z-index:2;background:#0b0e17}
.hl code{font:inherit;white-space:pre}
/* The editor surface is always dark, so its text uses fixed light colors
   (not theme vars, which would flip to dark and fail contrast in light mode). */
.gutter{position:absolute;left:1px;top:1px;bottom:1px;width:3em;z-index:3;overflow:hidden;
padding:1rem .5rem 1rem 0;text-align:right;color:#8089a8;
font:15px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;white-space:pre;
background:#0b0e17;border-right:1px solid var(--border);border-radius:10px 0 0 10px;
pointer-events:none;display:none}
.hl-on .hl{display:block}.hl-on .gutter{display:block}
.hl-on .editor-wrap textarea{color:transparent;background:transparent;caret-color:#f5f6ff}
.hl-on .editor-wrap textarea,.hl-on .hl{padding-left:3.6em}
.hl-on .hl code{padding-left:0}
.tk-cmd{color:#bd93f9;font-weight:600}.tk-num{color:#8be9fd}
.tk-str{color:#7ef0a0}.tk-com{color:#7e88a8;font-style:italic}.tk-par{color:#8089a8}
.errbar{display:none;margin:.5rem 0 0;padding:.5rem .7rem;border-radius:8px;font-size:.82rem;
background:rgba(255,85,85,.12);border:1px solid rgba(255,85,85,.4);color:#ff9b9b;
font-family:ui-monospace,Menlo,monospace;white-space:pre-wrap;word-break:break-word}
.errbar.show{display:block}
.toolbar{display:flex;flex-wrap:wrap;gap:.55rem;margin-top:.8rem}
button,.btn{font:600 15px/1 system-ui,sans-serif;cursor:pointer;border:none;border-radius:10px;
padding:.75rem 1.1rem;color:var(--btn-text);background:var(--purple);display:inline-flex;align-items:center;
gap:.4rem;transition:filter .15s,transform .05s}
button:hover,.btn:hover{filter:brightness(1.08);text-decoration:none}
button:active,.btn:active{transform:translateY(1px)}
.btn-ghost{background:transparent;color:var(--text);border:1px solid var(--border2)}
.btn-cyan{background:var(--cyan)}.btn-pink{background:var(--pink)}
.stage{background:#000;border:1px solid var(--border);border-radius:var(--radius);padding:.55rem;overflow:hidden}
.stage svg{width:100%;height:auto;display:block}
.hint{color:var(--muted);font-size:.85rem;margin:.55rem 0 0}
kbd{font:600 11px ui-monospace,Menlo,monospace;background:#0b0e17;border:1px solid var(--border2);
border-bottom-width:2px;border-radius:5px;padding:.08rem .35rem;color:#8be9fd}
#status{color:var(--green)}
.examples{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:.6rem}
.ex-form{margin:0;display:block}
.ex{width:100%;padding:.7rem .8rem;text-align:left;background:var(--panel2);border:1px solid var(--border);
border-radius:10px;color:var(--text);font-weight:700;font-size:.9rem;flex-direction:column;align-items:flex-start}
.ex:hover{border-color:var(--purple);color:var(--purple);filter:none}
.ex small{display:block;color:var(--muted);font-weight:400;font-size:.72rem;margin-top:.15rem}
.file-row{display:flex;flex-wrap:wrap;gap:.6rem;align-items:center}
input[type=file]{color:var(--muted);font-size:.9rem;max-width:100%}
input[type=file]::file-selector-button{font:600 14px system-ui;margin-right:.6rem;padding:.6rem .9rem;
border:none;border-radius:8px;background:var(--cyan);color:#0b0e17;cursor:pointer}
details.cheat{margin-top:1.15rem;background:var(--panel);border:1px solid var(--border);
border-radius:var(--radius);padding:.6rem 1.1rem}
details.cheat>summary{cursor:pointer;font-weight:700;color:var(--text);padding:.5rem 0}
.cheat-grid{display:grid;gap:1rem;grid-template-columns:1fr;margin-top:.5rem}
@media(min-width:640px){.cheat-grid{grid-template-columns:1fr 1fr}}
@media(min-width:1000px){.cheat-grid{grid-template-columns:repeat(auto-fit,minmax(180px,1fr))}}
.cheat-grid h3{color:var(--cyan);font-size:.78rem;text-transform:uppercase;letter-spacing:.05em;margin:.1rem 0 .5rem}
.cheat-grid ul{list-style:none;margin:0;padding:0}.cheat-grid li{margin:.35rem 0}
code{background:#0b0e17;border:1px solid var(--border);padding:.14rem .42rem;border-radius:6px;
font:12.5px ui-monospace,Menlo,monospace;color:#7ef0a0;white-space:nowrap}
footer{text-align:center;color:var(--muted);font-size:.85rem;margin-top:2rem;padding-top:1rem;border-top:1px solid var(--border)}
.toast{position:fixed;left:50%;bottom:1.2rem;transform:translateX(-50%) translateY(150%);background:var(--panel2);
border:1px solid var(--border2);color:var(--text);padding:.7rem 1.1rem;border-radius:10px;
box-shadow:0 10px 30px rgba(0,0,0,.4);transition:transform .25s;z-index:50}
.toast.show{transform:translateX(-50%) translateY(0)}
@media(prefers-reduced-motion:reduce){*{transition:none!important}}
.heronav{margin-top:.8rem}
.saverow{display:flex;gap:.55rem;margin-top:.7rem;flex-wrap:wrap}
.titlein{flex:1;min-width:160px;background:#0b0e17;color:#f5f6ff;border:1px solid var(--border);
border-radius:10px;padding:.7rem .9rem;font:15px system-ui,sans-serif}
.titlein::placeholder{color:#6b7490}
.flash{margin:0 0 .8rem;padding:.6rem .9rem;border-radius:10px;font-size:.9rem;
background:rgba(255,184,108,.14);border:1px solid rgba(255,184,108,.5);color:#ffcf99}
.gallery{display:grid;gap:1.1rem;grid-template-columns:repeat(auto-fill,minmax(240px,1fr))}
.gcard{margin:0;background:linear-gradient(180deg,var(--panel),var(--bg2));border:1px solid var(--border);
border-radius:var(--radius);overflow:hidden;box-shadow:0 10px 24px rgba(0,0,0,.3);
transition:transform .12s,border-color .12s}
.gcard:hover{transform:translateY(-3px);border-color:var(--purple)}
.gthumb{display:block;background:#000;line-height:0}
.gthumb img{width:100%;height:auto;display:block;aspect-ratio:3/2;object-fit:contain}
.gcap{display:flex;align-items:center;justify-content:space-between;gap:.5rem;padding:.6rem .8rem}
.gtitle{font-weight:600;font-size:.9rem;color:var(--text);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.gactions{display:flex;align-items:center;gap:.5rem;flex:none}
.gopen{font-size:.8rem;white-space:nowrap;color:var(--cyan)}
.likebtn{background:transparent;border:1px solid var(--border2);color:var(--muted);
font:600 .78rem system-ui,sans-serif;padding:.22rem .55rem;border-radius:999px;cursor:pointer;
display:inline-flex;align-items:center;gap:.15rem;transition:color .12s,border-color .12s}
.likebtn:hover,.likebtn.liked{color:var(--pink);border-color:var(--pink)}
.likebtn[disabled]{cursor:default}
")

;; Served from /app.js (CSP script-src 'self'), so it can use < > & freely.
;; Progressive enhancement: the page is fully usable without it (plain POST
;; forms). It adds live preview, Ctrl+Enter, Tab indent, PNG export, share
;; links, copy and a "surprise me" generator.
(define PAGE-JS #<<ENDJS
(function(){
  "use strict";
  var ta = document.getElementById('code');
  var stage = document.getElementById('stage');
  var statusEl = document.getElementById('status');
  var toastEl = document.getElementById('toast');
  var hl = document.getElementById('hl');
  var hlcode = document.getElementById('hlcode');
  var gutter = document.getElementById('gutter');
  var errbar = document.getElementById('errbar');
  var tt, deb;

  function bind(id, fn){ var el = document.getElementById(id); if (el){ el.addEventListener('click', fn); } }
  function toast(m){ if (!toastEl) return; toastEl.textContent = m; toastEl.classList.add('show');
    clearTimeout(tt); tt = setTimeout(function(){ toastEl.classList.remove('show'); }, 1800); }
  function setStatus(m){ if (statusEl) statusEl.textContent = m; }

  // ---- syntax highlighting (overlay under the textarea) ------------------
  var KW = {};
  ("circle rect ellipse line ring arc triangle poly heart sector spiral curve " +
   "polygon polyline star text bg repeat for grid let seed group rotate translate " +
   "scale opacity spin pulse blur glow shadow rgb rgba hsl hsla hsv palette mix " +
   "linear-bg radial-bg mod pow sin cos tan atan atan2 sqrt exp log abs neg sign " +
   "floor round ceil min max hypot dist lerp clamp map noise random pi tau width height"
  ).split(' ').forEach(function(k){ KW[k] = 1; });

  function esc(s){ return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }
  function highlight(src){
    var out = '', i = 0, n = src.length;
    while (i < n){
      var c = src[i];
      if (c === ';'){ var j = src.indexOf('\n', i); if (j < 0) j = n;
        out += '<span class="tk-com">' + esc(src.slice(i, j)) + '</span>'; i = j; }
      else if (c === '"'){ var j = i + 1; while (j < n && src[j] !== '"') j++; if (j < n) j++;
        out += '<span class="tk-str">' + esc(src.slice(i, j)) + '</span>'; i = j; }
      else if (c === '(' || c === ')'){ out += '<span class="tk-par">' + c + '</span>'; i++; }
      else if (/[0-9]/.test(c) || (c === '-' && /[0-9.]/.test(src[i+1] || ''))){
        var j = i + 1; while (j < n && /[0-9.eE+-]/.test(src[j])) j++;
        out += '<span class="tk-num">' + esc(src.slice(i, j)) + '</span>'; i = j; }
      else if (/[a-zA-Z]/.test(c)){
        var j = i + 1; while (j < n && /[a-zA-Z0-9?*+\/<>=!-]/.test(src[j])) j++;
        var w = src.slice(i, j);
        out += KW[w] ? '<span class="tk-cmd">' + esc(w) + '</span>' : esc(w); i = j; }
      else { out += esc(c); i++; }
    }
    return out;
  }
  function syncEditor(){
    if (!ta || !hlcode) return;
    var v = ta.value;
    hlcode.innerHTML = highlight(v) + '\n';
    if (gutter){
      var lines = v.split('\n').length, g = '';
      for (var k = 1; k <= lines; k++) g += k + '\n';
      gutter.textContent = g;
    }
    syncScroll();
  }
  function syncScroll(){
    if (hl && ta){ hl.scrollTop = ta.scrollTop; hl.scrollLeft = ta.scrollLeft; }
    if (gutter && ta){ gutter.scrollTop = ta.scrollTop; }
  }

  // ---- live render -------------------------------------------------------
  var inflight = false, pending = false;
  function render(){
    if (!ta || !stage) return;
    if (inflight){ pending = true; return; }
    inflight = true; setStatus('se randeaza...');
    var t0 = performance.now();
    fetch('/api/render', { method:'POST',
        headers:{ 'Content-Type':'application/x-www-form-urlencoded' },
        body:'code=' + encodeURIComponent(ta.value) })
      .then(function(r){ var ms = r.headers.get('X-Render-Ms'), el = r.headers.get('X-Elements');
        return r.text().then(function(t){ return { t:t, ms:ms, el:el }; }); })
      .then(function(o){ stage.innerHTML = o.t;
        var ms = (o.ms != null) ? o.ms : Math.round(performance.now() - t0);
        setStatus((o.el || '?') + ' elemente · ' + ms + ' ms'); showErrors(); })
      .catch(function(){ setStatus('eroare de retea'); })
      .then(function(){ inflight = false; if (pending){ pending = false; render(); } });
  }
  function scheduleRender(){ clearTimeout(deb); deb = setTimeout(render, 450); }

  // Surface interpreter error nodes (fill="#ff5555") from the rendered SVG.
  function showErrors(){
    if (!errbar || !stage) return;
    var nodes = stage.querySelectorAll('text[fill="#ff5555"]');
    if (!nodes.length){ errbar.classList.remove('show'); errbar.textContent = ''; return; }
    var msgs = [];
    for (var k = 0; k < nodes.length && k < 6; k++) msgs.push('⚠ ' + nodes[k].textContent);
    errbar.textContent = msgs.join('\n'); errbar.classList.add('show');
  }

  // Insert text at the caret, keep the selection sensible, refresh the editor.
  function setRange(value, start, end){
    ta.value = value; ta.selectionStart = start; ta.selectionEnd = (end == null ? start : end);
    syncEditor();
  }
  var PAIRS = { '(' : ')', '"' : '"' };

  if (ta){
    ta.addEventListener('input', function(){ syncEditor(); scheduleRender(); });
    ta.addEventListener('scroll', syncScroll);
    ta.addEventListener('keydown', function(e){
      var s = ta.selectionStart, en = ta.selectionEnd, v = ta.value;
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter'){ e.preventDefault(); clearTimeout(deb); render(); return; }
      if (e.key === 'Tab'){ e.preventDefault();
        setRange(v.slice(0, s) + '  ' + v.slice(en), s + 2); scheduleRender(); return; }
      if (e.ctrlKey || e.metaKey || e.altKey) return;
      // skip over a closing char typed right before itself (checked first so a
      // closing " isn't mistaken for a new opening pair)
      if ((e.key === ')' || e.key === '"') && s === en && v[s] === e.key){
        e.preventDefault(); setRange(v, s + 1); return;
      }
      // auto-close ( and " (quotes only on an empty selection)
      if (PAIRS[e.key] && (e.key !== '"' || s === en)){
        e.preventDefault();
        setRange(v.slice(0, s) + e.key + PAIRS[e.key] + v.slice(en), s + 1);
        scheduleRender(); return;
      }
      // backspace empties a matching pair in one keystroke
      if (e.key === 'Backspace' && s === en && s > 0 && PAIRS[v[s-1]] === v[s]){
        e.preventDefault(); setRange(v.slice(0, s-1) + v.slice(s+1), s-1); scheduleRender(); return;
      }
    });
  }

  // Intercept the "Randeaza" submit so JS users get a live render with no
  // full-page reload; "Download SVG" still submits normally, and with JS off
  // both buttons POST the form as before.
  var form = document.getElementById('editForm');
  if (form){
    form.addEventListener('submit', function(e){
      var btn = e.submitter;
      if (btn && btn.value === 'preview'){ e.preventDefault(); clearTimeout(deb); render(); return; }
      // Save without leaving the editor (no-JS falls back to the form POST).
      if (btn && btn.value === 'save'){
        e.preventDefault();
        var ti = form.querySelector('input[name="title"]');
        var title = ti ? ti.value : '';
        btn.disabled = true;
        fetch('/api/save', { method:'POST',
            headers:{ 'Content-Type':'application/x-www-form-urlencoded' },
            body:'code=' + encodeURIComponent(ta.value) + '&title=' + encodeURIComponent(title) })
          .then(function(r){ return r.json(); })
          .then(function(o){ toast(o && o.msg ? o.msg : 'Salvat');
            if (o && o.ok && ti){ ti.value = ''; } })
          .catch(function(){ toast('Eroare la salvare'); })
          .then(function(){ btn.disabled = false; });
      }
    });
  }

  // ---- copy / share ------------------------------------------------------
  function fallbackCopy(){ if (ta){ ta.focus(); ta.select(); } try{ document.execCommand('copy'); }catch(e){} }
  function copyText(text, msg){
    if (navigator.clipboard && navigator.clipboard.writeText){
      navigator.clipboard.writeText(text).then(function(){ toast(msg); }, function(){ fallbackCopy(); toast(msg); });
    } else { fallbackCopy(); toast(msg); }
  }
  bind('btnCopy', function(){ if (ta) copyText(ta.value, 'Cod copiat'); });

  function encode(code){ return encodeURIComponent(btoa(unescape(encodeURIComponent(code)))); }
  bind('btnShare', function(){
    if (!ta) return;
    var enc = encode(ta.value);
    if (enc.length > 8000){ toast('Cod prea mare pentru link — foloseste Download SVG'); return; }
    var url = location.origin + location.pathname + '?c=' + enc;
    copyText(url, 'Link copiat in clipboard');
    try{ history.replaceState(null, '', url); } catch(e){}
  });

  // ---- PNG export (client-side rasterization) ----------------------------
  bind('btnPng', function(){
    var svg = stage ? stage.querySelector('svg') : null;
    if (!svg){ toast('Nimic de exportat'); return; }
    var xml = new XMLSerializer().serializeToString(svg);
    var img = new Image();
    img.onload = function(){
      var scale = 2, c = document.createElement('canvas');
      c.width = 600 * scale; c.height = 400 * scale;
      var cx = c.getContext('2d');
      cx.fillStyle = '#000'; cx.fillRect(0, 0, c.width, c.height);
      cx.setTransform(scale, 0, 0, scale, 0, 0);
      cx.drawImage(img, 0, 0, 600, 400);
      c.toBlob(function(b){
        if (!b){ toast('PNG esuat'); return; }
        var a = document.createElement('a');
        a.href = URL.createObjectURL(b); a.download = 'procedural_art.png';
        document.body.appendChild(a); a.click(); a.remove();
        setTimeout(function(){ URL.revokeObjectURL(a.href); }, 2000);
        toast('PNG descarcat');
      }, 'image/png');
    };
    img.onerror = function(){ toast('PNG esuat'); };
    img.src = 'data:image/svg+xml;base64,' + btoa(unescape(encodeURIComponent(xml)));
  });

  // ---- surprise me -------------------------------------------------------
  function ri(a, b){ return a + Math.floor(Math.random() * (b - a + 1)); }
  function rf(a, b){ return (a + Math.random() * (b - a)).toFixed(2); }
  var templates = [
    function(s){ return '(linear-bg ' + ri(0,180) + ' "#05070f" "#1a1030")\n(seed ' + s + ')\n(repeat 1200\n  (let ([x (random 600)] [y (random 400)]\n        [a (* 6.28 (noise (* x 0.01) (* y 0.01)))])\n    (line x y (+ x (* 16 (cos a))) (+ y (* 16 (sin a)))\n          (mix "#8be9fd" "#ff79c6" (noise (* x 0.02) (* y 0.02))) 1.4)))'; },
    function(s){ return '(bg "#0b0f1a")\n(seed ' + s + ')\n(spin 300 200 ' + ri(16,38) + '\n  (repeat ' + ri(70,140) + '\n    (circle (+ 300 (* (* i 2.2) (cos (* i ' + rf(0.2,0.45) + ')))) (+ 200 (* (* i 2.2) (sin (* i ' + rf(0.2,0.45) + ')))) 6 (hsl (* i ' + ri(3,8) + ') 85 60))))'; },
    function(s){ return '(radial-bg "#fff3b0" "#ff8c42" "#1a0b2e")\n(seed ' + s + ')\n(repeat 12\n  (rotate (* i 30) 300 200\n    (repeat 14\n      (star (+ 300 (* i 16)) 200 5 10 4 (hsla (* i 24) 80 62 0.7)))))'; },
    function(s){ return '(bg "#05070f")\n(seed ' + s + ')\n(repeat 90\n  (let ([a (* i 0.18)] [r (* 170 (cos (* ' + ri(3,7) + ' (* i 0.18))))])\n    (circle (+ 300 (* r (cos a))) (+ 200 (* r (sin a))) 5 (mix "#50fa7b" "#8be9fd" (map i 0 90 0 1)))))'; },
    function(s){ return '(linear-bg 90 "#0a0a12" "#161032")\n(seed ' + s + ')\n(pulse 3\n  (repeat 60\n    (ring (random 600) (random 400) (random 6 40) (hsl (random 360) 75 62) 2)))'; }
  ];
  bind('btnSurprise', function(){
    if (!ta) return;
    ta.value = templates[ri(0, templates.length - 1)](ri(1, 99999));
    syncEditor(); clearTimeout(deb); render(); toast('Surpriza!');
  });

  // ---- theme toggle ------------------------------------------------------
  bind('btnTheme', function(){
    var root = document.documentElement;
    var next = root.getAttribute('data-theme') === 'light' ? 'dark' : 'light';
    root.setAttribute('data-theme', next);
    try{ localStorage.setItem('theme', next); }catch(e){}
    toast(next === 'light' ? 'Tema deschisa' : 'Tema intunecata');
  });

  // ---- file-name display -------------------------------------------------
  var f = document.getElementById('image_file');
  if (f){ f.addEventListener('change', function(){ var n = document.getElementById('fname');
    if (n){ n.textContent = f.files[0] ? f.files[0].name : ''; } }); }

  // ---- gallery: like buttons (event delegation; no-op off the gallery) ----
  document.addEventListener('click', function(e){
    var btn = e.target && e.target.closest ? e.target.closest('.likebtn') : null;
    if (!btn || btn.disabled) return;
    var id = btn.getAttribute('data-id'); if (!id) return;
    btn.disabled = true;
    fetch('/api/like', { method:'POST',
        headers:{ 'Content-Type':'application/x-www-form-urlencoded' },
        body:'id=' + encodeURIComponent(id) })
      .then(function(r){ return r.json(); })
      .then(function(o){
        var cnt = btn.querySelector('.likecount');
        if (o && typeof o.likes === 'number' && cnt) cnt.textContent = o.likes;
        btn.classList.add('liked');
        if (o && !o.ok) toast('Ai apreciat deja asta');
      })
      .catch(function(){ btn.disabled = false; });
  });

  // ---- enable the pro editor + surface any errors already on the canvas --
  if (ta && hl && hlcode){ document.body.classList.add('hl-on'); syncEditor(); }
  showErrors();
})();
ENDJS
)

;; Content hash of the script, used to cache-bust /app.js?v=... so a deploy is
;; picked up immediately instead of waiting for the CDN/browser cache to expire.
(define APP-JS-VER (substring (sha1 (open-input-bytes (string->bytes/utf-8 PAGE-JS))) 0 10))

;; Preset programs — each is a plain POST form, so they work without JS.
(define EXAMPLES
  (list
   (list "Vartej" "spirala trig" DEFAULT-CODE)
   (list "Curcubeu" "benzi hsl"
         "(repeat 24 (rect (* i 25) 0 26 400 (hsl (* i 15) 80 55)))")
   (list "Cer instelat" "random + luna"
         "(bg \"#05070f\")\n(repeat 160 (circle (random 600) (random 400) (random 1 3) \"#ffffff\"))\n(circle 480 90 42 \"#f1fa8c\")")
   (list "Floare" "roza polara"
         "(bg \"#0b0f1a\")\n(repeat 140\n  (let ([a (* i 0.2)] [r (* 160 (cos (* 5 (* i 0.2))))])\n    (circle (+ 300 (* r (cos a))) (+ 200 (* r (sin a))) 5 (hsl (* i 3) 90 62))))")
   (list "Grila" "repeat imbricat"
         "(bg \"#0e1017\")\n(repeat 10\n  (let ([col i])\n    (repeat 7\n      (star (+ 40 (* col 58)) (+ 40 (* i 55)) 5 18 8 (hsl (* (+ (* col 7) i) 8) 78 62)))))")
   (list "Unda" "sinusoida"
         "(bg \"#0b0f1a\")\n(repeat 60\n  (circle (* i 10) (+ 200 (* 120 (sin (* i 0.3)))) 6 (hsl (* i 6) 85 60)))")
   (list "Camp de flux" "noise organic"
         "(linear-bg 90 \"#05070f\" \"#0f1630\")\n(seed 7)\n(repeat 1400\n  (let ([x (random 600)] [y (random 400)]\n        [a (* 6.28 (noise (* x 0.012) (* y 0.012)))])\n    (line x y (+ x (* 14 (cos a))) (+ y (* 14 (sin a)))\n          (mix \"#8be9fd\" \"#bd93f9\" (noise (* x 0.02) (* y 0.02))) 1.5)))")
   (list "Soare" "gradient radial"
         "(radial-bg \"#fff3b0\" \"#ff8c42\" \"#b23a48\" \"#0b0f1a\")\n(spin 300 200 60\n  (repeat 36\n    (line 300 200 (+ 300 (* 260 (cos (* i 0.1745)))) (+ 200 (* 260 (sin (* i 0.1745))))\n          (rgba 255 240 180 0.5) 2)))\n(circle 300 200 70 \"#fff3b0\")")
   (list "Caleidoscop" "rotate + repeat"
         "(bg \"#0a0a12\")\n(repeat 12\n  (rotate (* i 30) 300 200\n    (repeat 10\n      (let ([r (* i 4)])\n        (circle (+ 300 (* (* i 10) (cos (* i 0.5)))) 200 (+ 3 r)\n                (hsla (* i 20) 80 60 0.7))))))")
   (list "Spirala animata" "spin + stele"
         "(linear-bg 45 \"#1a0b2e\" \"#0b0f1a\")\n(spin 300 200 24\n  (repeat 40\n    (let ([a (* i 0.5)] [r (* i 6)])\n      (star (+ 300 (* r (cos a))) (+ 200 (* r (sin a))) 5 8 3\n            (mix \"#f1fa8c\" \"#ff79c6\" (map i 0 40 0 1))))))")
   (list "Caroiaj" "grid + hsv"
         "(bg \"#0a0a12\")\n(grid 20 14\n  (let ([x (+ 20 (* gx 30))] [y (+ 20 (* gy 28))])\n    (poly x y (+ 3 (mod gi 5)) 11\n          (hsv (* (+ gx gy) 12) 80 95))))")
   (list "Inimi" "grid + heart"
         "(linear-bg 90 \"#2a0a1a\" \"#0b0f1a\")\n(grid 8 5\n  (let ([x (+ 45 (* gx 72))] [y (+ 55 (* gy 80))])\n    (pulse (+ 1.5 (* gi 0.1))\n      (heart x y (+ 16 (* 4 (noise gx gy))) (hsl (* gi 9) 80 65)))))")
   (list "Raze" "bucla for"
         "(radial-bg \"#10131f\" \"#05070f\")\n(for a 0 360 6\n  (line 300 200 (+ 300 (* 230 (cos (* a 0.0175)))) (+ 200 (* 230 (sin (* a 0.0175))))\n        (hsv a 85 95) 2))\n(circle 300 200 30 \"#f1fa8c\")")
   (list "Nebuloasa" "glow + palette"
         "(bg \"#02030a\")\n(seed 11)\n(glow \"#00e5ff\"\n  (repeat 220\n    (let ([x (random 600)] [y (random 400)])\n      (circle x y (random 2 6) (palette \"neon\" (random 6))))))")
   (list "Spirala" "spiral + glow"
         "(radial-bg \"#0a0012\" \"#000\")\n(glow \"#ff2a6d\"\n  (spiral 300 200 6 4 180 (palette \"neon\" 0) 3))\n(spin 300 200 24\n  (spiral 300 200 6 6 170 \"#00e5ff\" 2))")
   (list "Val" "curba neteda"
         "(linear-bg 90 \"#031d2e\" \"#06374f\")\n(repeat 6\n  (let ([o (* i 14)])\n    (curve (palette \"ocean\" (+ i 1)) 3\n      0 (+ 200 o) 100 (+ 150 o) 200 (+ 230 o) 300 (+ 160 o)\n      400 (+ 240 o) 500 (+ 170 o) 600 (+ 210 o))))")
   (list "Petale" "sector radial"
         "(bg \"#0b0f1a\")\n(repeat 18\n  (rotate (* i 20) 300 200\n    (sector 300 200 160 -8 8 (hsv (* i 20) 75 95))))\n(glow \"#ffffff\" (circle 300 200 26 \"#fff3b0\"))")
   (list "Bile gradient" "linear per-forma"
         "(linear-bg 90 \"#0b0f1a\" \"#161032\")\n(repeat 30\n  (circle (random 600) (random 400) (random 20 48)\n          (linear (random 360) (palette \"neon\" (random 6)) \"#0b0f1a\")))")
   (list "Orbite" "contur + dash"
         "(bg \"#05070f\")\n(repeat 7\n  (stroke (hsv (* i 50) 80 95) 2\n    (dash 6 10\n      (ellipse 300 200 (+ 40 (* i 38)) (+ 24 (* i 22)) \"none\"))))\n(glow \"#f1fa8c\" (circle 300 200 14 \"#f1fa8c\"))")))

(define (example-card title desc code)
  `(form ((method "post") (class "ex-form"))
     (input ((type "hidden") (name "action") (value "preview")))
     (input ((type "hidden") (name "code") (value ,code)))
     (button ((type "submit") (class "ex")) ,title (small ,desc))))

(define (cheat-col heading items)
  `(div (h3 ,heading)
        (ul ,@(for/list ([it (in-list items)]) `(li (code ,it))))))

;; Shared bits so the gallery page matches the editor page's chrome.
(define FAVICON-HREF
  "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='7' fill='%230b0d14'/%3E%3Ccircle cx='16' cy='16' r='9' fill='%23bd93f9'/%3E%3C/svg%3E")
(define THEME-BOOT
  "try{var t=localStorage.getItem('theme');if(t){document.documentElement.setAttribute('data-theme',t);}}catch(e){}")

;; ---------------------------------------------------------------------------
;; Community gallery page.  Thumbnails are <img> to /thumb/<id> (inert SVG),
;; each linking back into the editor via a ?c= permalink.
;; ---------------------------------------------------------------------------
(define (gallery-card row)
  (define id (vector-ref row 0))
  (define title (vector-ref row 1))
  (define href (string-append "/?c=" (encode-share (vector-ref row 2))))
  (define likes (if (>= (vector-length row) 4) (vector-ref row 3) 0))
  `(figure ((class "gcard"))
     (a ((class "gthumb") (href ,href) (title "Deschide in editor"))
        (img ((src ,(format "/thumb/~a" id)) (alt ,title) (loading "lazy")
              (width "600") (height "400"))))
     (figcaption ((class "gcap"))
        (span ((class "gtitle")) ,title)
        (span ((class "gactions"))
          (button ((type "button") (class "likebtn") (data-id ,(number->string id))
                   (aria-label "Apreciaza"))
                  "♥ " (span ((class "likecount")) ,(number->string likes)))
          (a ((class "gopen") (href ,href)) "Deschide ↗")))))

(define (gallery-page before [sort 'recent])
  (define rows (gallery-list before sort))
  (define last-id (and (pair? rows) (= (length rows) GALLERY-PAGE)
                       (vector-ref (last rows) 0)))
  (response/xexpr
   #:preamble #"<!DOCTYPE html>"
   `(html ((lang "ro"))
     (head
      (meta ((charset "utf-8")))
      (title "Galerie — Procedural Canvas DSL")
      (meta ((name "viewport") (content "width=device-width, initial-scale=1")))
      (meta ((name "color-scheme") (content "dark light")))
      (meta ((name "theme-color") (content "#0b0d14")))
      (meta ((name "description") (content "Creatii generative salvate de comunitate in Procedural Canvas DSL — apasa pentru a deschide in editor.")))
      (link ((rel "canonical") (href "https://racket.micutu.com/gallery")))
      (link ((rel "icon") (href ,FAVICON-HREF)))
      (style ,PAGE-CSS)
      (script ,THEME-BOOT)
      (script ((src ,(string-append "/app.js?v=" APP-JS-VER)) (defer "defer"))))
     (body
      (div ((class "wrap"))
       (header ((class "hero"))
        (div ((class "badge")) "Galerie comunitara")
        (h1 "Creatii salvate")
        (p "Arta trimisa de vizitatori. Apasa o miniatura ca sa o deschizi si sa o modifici in editor.")
        (p ((class "heronav"))
           (a ((href "/") (class "btn btn-ghost")) "← Inapoi la editor")
           " "
           (a ((href "/gallery") (class ,(if (eq? sort 'popular) "btn btn-ghost" "btn btn-cyan"))) "Recente")
           " "
           (a ((href "/gallery?sort=popular") (class ,(if (eq? sort 'popular) "btn btn-cyan" "btn btn-ghost"))) "★ Populare")))
       (main ((id "main"))
        ,(if (null? rows)
             `(p ((class "hint") (style "text-align:center;padding:2rem 0"))
                 "Inca nu exista creatii salvate. Fii primul: randeaza ceva in editor si apasa „Salveaza in galerie”.")
             `(div ((class "gallery")) ,@(map gallery-card rows)))
        ,@(if (and last-id (not (eq? sort 'popular)))
              (list `(p ((style "text-align:center;margin-top:1.4rem"))
                        (a ((href ,(format "/gallery?before=~a" last-id)) (class "btn btn-ghost"))
                           "Mai vechi →")))
              '()))
       (footer
        (p "Procedural Canvas DSL · "
           (a ((href "/")) "editor"))))))))

(define (start req)
  ;; The web-server body parser throws on malformed / non-UTF-8 form bodies;
  ;; swallow that so a hostile request degrades to empty bindings, not a 500.
  (define bindings
    (with-handlers ([exn:fail? (lambda (_) '())])
      (request-bindings/raw req)))

  (define (extract-form-value key)
    (define b (bindings-assq key bindings))
    (if (and b (binding:form? b)) (bytes->string* (binding:form-value b)) ""))

  (define (extract-file-content key)
    (define b (bindings-assq key bindings))
    (if (and b (binding:file? b)) (binding:file-content b) #f))

  (cond
    ;; Lightweight health endpoint for monitoring / uptime checks.
    [(equal? (req-path req) "health")
     (response/full 200 #"OK" (current-seconds) #"text/plain" '() (list #"ok"))]

    ;; Open Graph / Twitter share image (rendered once, cached).
    [(equal? (req-path req) "og.png")
     (response/full 200 #"OK" (current-seconds) #"image/png"
                    (list (make-header #"Cache-Control" #"public, max-age=86400"))
                    (list (og-png-bytes)))]

    ;; Minimal sitemap for the single public page.
    [(equal? (req-path req) "sitemap.xml")
     (response/full 200 #"OK" (current-seconds) #"application/xml; charset=utf-8"
                    (list (make-header #"Cache-Control" #"public, max-age=86400"))
                    (list (string->bytes/utf-8
                           (string-append
                            "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
                            "<urlset xmlns=\"http://www.sitemaps.org/schemas/sitemap/0.9\">"
                            "<url><loc>https://racket.micutu.com/</loc><changefreq>weekly</changefreq><priority>1.0</priority></url>"
                            "</urlset>"))))]

    ;; Front-end script, served from same origin (CSP script-src 'self').
    [(equal? (req-path req) "app.js")
     ;; Versioned via ?v=<hash> in the page, so this can cache hard.
     (response/full 200 #"OK" (current-seconds) #"application/javascript; charset=utf-8"
                    (list (make-header #"Cache-Control" #"public, max-age=604800, immutable"))
                    (list (string->bytes/utf-8 PAGE-JS)))]

    ;; Live-preview API: POST code -> SVG, with render stats in headers.  Same
    ;; strict caps as the page render; used by the debounced editor.
    [(equal? (req-path req) "api/render")
     (define code (extract-form-value #"code"))
     (define t0 (current-inexact-milliseconds))
     (define svg (parse-to-svg (if (non-empty-string? code) code DEFAULT-CODE)))
     (define ms (inexact->exact (round (- (current-inexact-milliseconds) t0))))
     (response/full
      200 #"OK" (current-seconds) #"image/svg+xml; charset=utf-8"
      (list (make-header #"X-Render-Ms" (string->bytes/utf-8 (number->string ms)))
            (make-header #"X-Elements" (string->bytes/utf-8 (number->string (count-svg-nodes svg))))
            (make-header #"Cache-Control" #"no-store"))
      (list (string->bytes/utf-8 (xexpr->string svg))))]

    ;; Like a creation once per IP; returns the new count (JSON).
    [(equal? (req-path req) "api/like")
     (define likes (gallery-like! (string->number (extract-form-value #"id")) (req-ip req)))
     (response/full 200 #"OK" (current-seconds) #"application/json; charset=utf-8"
                    (list (make-header #"Cache-Control" #"no-store"))
                    (list (string->bytes/utf-8
                           (jsexpr->string (hasheq 'ok (and likes #t) 'likes (or likes 0))))))]

    ;; JSON save endpoint for the no-reload save button (same caps as the form).
    [(equal? (req-path req) "api/save")
     (define-values (ok? msg)
       (gallery-save! (extract-form-value #"title") (extract-form-value #"code") (req-ip req)))
     (response/full 200 #"OK" (current-seconds) #"application/json; charset=utf-8"
                    (list (make-header #"Cache-Control" #"no-store"))
                    (list (string->bytes/utf-8 (jsexpr->string (hasheq 'ok ok? 'msg msg)))))]

    ;; Gallery thumbnail: stored SVG served as an inert image (never inlined).
    [(regexp-match #px"^thumb/([0-9]{1,12})$" (req-path req))
     => (lambda (m)
          (define svg (gallery-svg (string->number (cadr m))))
          (if svg
              (response/full 200 #"OK" (current-seconds) #"image/svg+xml; charset=utf-8"
                             (list (make-header #"Cache-Control" #"public, max-age=86400, immutable"))
                             (list (string->bytes/utf-8 svg)))
              (response/full 404 #"Not Found" (current-seconds) #"text/plain" '() (list #"not found"))))]

    ;; Community gallery page.
    [(equal? (req-path req) "gallery")
     (define before (string->number (extract-form-value #"before")))
     (define sort (if (equal? (extract-form-value #"sort") "popular") 'popular 'recent))
     (gallery-page (and (exact-integer? before) before) sort)]

    [else
     (define action (extract-form-value #"action"))
     (define code-val (extract-form-value #"code"))
     (define uploaded-file (extract-file-content #"image_file"))

     (define initial-code
       (cond
         [(equal? action "upload")
          (cond
            [(not (and uploaded-file (bytes? uploaded-file) (> (bytes-length uploaded-file) 0)))
             ";; Eroare la incarcarea fisierului"]
            [(> (bytes-length uploaded-file) MAX-UPLOAD-BYTES)
             ";; Eroare: fisier prea mare (max 3 MB)."]
            [else (image->dsl uploaded-file)])]
         [(non-empty-string? code-val) code-val]
         ;; ?c= permalink (shared creation)
         [(decode-share (extract-form-value #"c")) => values]
         [else ""]))

     (define final-code
       (if (non-empty-string? initial-code) initial-code DEFAULT-CODE))

     ;; Saving to the gallery: on success send the author to the gallery (their
     ;; creation is at the top); on failure re-render the editor with the reason.
     (define-values (save-ok? save-msg)
       (if (equal? action "save")
           (gallery-save! (extract-form-value #"title") code-val (req-ip req))
           (values #f #f)))

     (cond
       [(and (equal? action "save") save-ok?)
        (redirect-to "/gallery" see-other)]
       [(equal? action "download")
        (response/full
         200 #"OK"
         (current-seconds) #"image/svg+xml"
         (list (make-header #"Content-Disposition" #"attachment; filename=\"procedural_art.svg\""))
         (list (string->bytes/utf-8 (xexpr->string (parse-to-svg final-code)))))]

       [else
        (response/xexpr
         #:preamble #"<!DOCTYPE html>"
         `(html ((lang "ro"))
           (head
            (meta ((charset "utf-8")))
            (title "Procedural Canvas DSL — arta SVG generativa in Racket")
            (meta ((name "viewport") (content "width=device-width, initial-scale=1")))
            (meta ((name "color-scheme") (content "dark light")))
            (meta ((name "theme-color") (content "#0b0d14")))
            (meta ((name "description")
                   (content "Un limbaj Lisp-like scris in Racket care transforma cod in arta SVG: bucle, trigonometrie, noise, gradienti, animatie si culori — randat pe server, descarcabil ca SVG sau PNG.")))
            (meta ((name "keywords")
                   (content "arta generativa, procedural, SVG, Racket, DSL, creative coding, noise, generative art")))
            (link ((rel "canonical") (href "https://racket.micutu.com/")))
            ;; Open Graph
            (meta ((property "og:type") (content "website")))
            (meta ((property "og:site_name") (content "Procedural Canvas DSL")))
            (meta ((property "og:title") (content "Procedural Canvas DSL — arta SVG generativa in Racket")))
            (meta ((property "og:description")
                   (content "Scrie cod Lisp, obtii arta SVG. Bucle, trigonometrie, noise, gradienti si animatie — totul randat pe server.")))
            (meta ((property "og:url") (content "https://racket.micutu.com/")))
            (meta ((property "og:image") (content "https://racket.micutu.com/og.png")))
            (meta ((property "og:image:width") (content "1200")))
            (meta ((property "og:image:height") (content "630")))
            (meta ((property "og:locale") (content "ro_RO")))
            ;; Twitter
            (meta ((name "twitter:card") (content "summary_large_image")))
            (meta ((name "twitter:title") (content "Procedural Canvas DSL")))
            (meta ((name "twitter:description")
                   (content "Scrie cod Lisp, obtii arta SVG generativa. Randat in Racket.")))
            (meta ((name "twitter:image") (content "https://racket.micutu.com/og.png")))
            (link ((rel "icon")
                   (href "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='7' fill='%230b0d14'/%3E%3Ccircle cx='16' cy='16' r='9' fill='%23bd93f9'/%3E%3C/svg%3E")))
            (link ((rel "sitemap") (type "application/xml") (href "/sitemap.xml")))
            ;; Structured data for search engines
            (script ((type "application/ld+json"))
                    ,(string-append
                      "{\"@context\":\"https://schema.org\",\"@type\":\"WebApplication\","
                      "\"name\":\"Procedural Canvas DSL\","
                      "\"url\":\"https://racket.micutu.com/\","
                      "\"applicationCategory\":\"DesignApplication\","
                      "\"operatingSystem\":\"Web\","
                      "\"description\":\"Un limbaj Lisp-like in Racket care randeaza arta SVG generativa din cod.\","
                      "\"offers\":{\"@type\":\"Offer\",\"price\":\"0\",\"priceCurrency\":\"EUR\"}}"))
            (style ,PAGE-CSS)
            ;; Apply the saved theme before first paint to avoid a flash.
            (script "try{var t=localStorage.getItem('theme');if(t){document.documentElement.setAttribute('data-theme',t);}}catch(e){}"))
           (body
            (div ((class "wrap"))
             (header ((class "hero"))
              (div ((class "badge")) "Racket · web-server · SVG")
              (h1 "Procedural Canvas DSL")
              (p "Scrie cod, obtii arta. Bucle, trigonometrie, culori si forme — totul randat pe server, apoi descarcabil ca SVG.")
              (p ((class "heronav")) (a ((href "/gallery") (class "btn btn-ghost")) "🖼 Galerie comunitara")))

             (main ((id "main"))
             (div ((class "grid"))
              (section ((class "panel"))
               (h2 "Editor")
               ,@(if (and (equal? action "save") save-msg)
                     (list `(div ((class "flash") (role "alert")) ,save-msg))
                     '())
               (form ((method "post") (id "editForm"))
                (div ((class "editor-wrap") (id "editorWrap"))
                 (div ((class "gutter") (id "gutter") (aria-hidden "true")) "")
                 (pre ((class "hl") (id "hl") (aria-hidden "true")) (code ((id "hlcode")) ""))
                 (textarea ((id "code") (name "code") (spellcheck "false") (wrap "off")
                            (autocomplete "off") (autocapitalize "off") (autocorrect "off")
                            (aria-label "Editor de cod DSL")
                            (placeholder "Codul tau aici...")) ,final-code))
                (div ((class "errbar") (id "errbar") (role "alert") (aria-live "assertive") (hidden "hidden")) "")
                (div ((class "toolbar"))
                 (button ((type "submit") (name "action") (value "preview")) "▶ Randeaza")
                 (button ((type "submit") (name "action") (value "download") (class "btn-cyan")) "⭳ SVG")
                 (button ((type "button") (id "btnPng") (class "btn-ghost")) "⤓ PNG")
                 (button ((type "button") (id "btnShare") (class "btn-ghost")) "🔗 Share")
                 (button ((type "button") (id "btnCopy") (class "btn-ghost")) "⧉ Copiaza")
                 (button ((type "button") (id "btnSurprise") (class "btn-pink")) "🎲 Surpriza")
                 (button ((type "button") (id "btnTheme") (class "btn-ghost") (title "Schimba tema")) "🌓 Tema")
                 (a ((href "/") (class "btn btn-ghost")) "↺ Reset"))
                (div ((class "saverow"))
                 (input ((type "text") (name "title") (maxlength "60") (class "titlein")
                         (placeholder "Titlu creatie...") (aria-label "Titlu pentru galerie")))
                 (button ((type "submit") (name "action") (value "save") (class "btn-cyan")) "💾 Salveaza in galerie")))
               (p ((class "hint"))
                  (span ((id "status") (aria-live "polite")) "Live: se randeaza pe masura ce scrii.")
                  " · " (kbd "Ctrl+Enter") " randeaza · " (kbd "Tab") " indenteaza."))

              (section ((class "panel"))
               (h2 "Panza (600 × 400)")
               (div ((class "stage") (id "stage") (role "img")
                     (aria-label "Panza cu arta generata din cod")) ,(parse-to-svg final-code))
               (h2 ((style "margin-top:1.15rem")) "Imagine → cod DSL")
               (form ((method "post") (enctype "multipart/form-data") (class "file-row"))
                (input ((type "hidden") (name "action") (value "upload")))
                (input ((type "file") (id "image_file") (name "image_file") (accept "image/png,image/jpeg")
                        (aria-label "Incarca o imagine JPG sau PNG")))
                (span ((id "fname") (class "hint")) "")
                (button ((type "submit") (class "btn-pink")) "Converteste"))
               (p ((class "hint")) "JPG/PNG, max 3 MB. Imaginea devine cerculete DSL pe care le poti edita.")))

             (section ((class "panel") (style "margin-top:1.15rem"))
              (h2 "Exemple — apasa pentru a incarca")
              (div ((class "examples")) ,@(map (lambda (e) (apply example-card e)) EXAMPLES)))

             (details ((class "cheat") (open "open"))
              (summary "Referinta limbaj (cheatsheet)")
              (div ((class "cheat-grid"))
               ,(cheat-col "Forme"
                  (list "(circle x y r culoare)" "(rect x y w h culoare)"
                        "(ellipse cx cy rx ry culoare)" "(line x1 y1 x2 y2 culoare gros)"
                        "(ring cx cy r culoare gros)" "(arc cx cy r a0 a1 culoare gros)"
                        "(triangle x1 y1 x2 y2 x3 y3 c)"
                        "(polygon culoare x1 y1 ...)" "(polyline culoare gros x1 y1 ...)"
                        "(star cx cy varfuri rext rint c)"
                        "(poly cx cy laturi r c)" "(heart cx cy marime c)"
                        "(sector cx cy r a0 a1 c)" "(spiral cx cy ture r0 r1 c gros)"
                        "(curve c gros x1 y1 x2 y2 ...)"
                        "(text x y marime culoare STR)" "(bg culoare)"))
               ,(cheat-col "Control"
                  (list "(repeat N cmd...)" "i = index in repeat"
                        "(for nume a b [pas] cmd...)" "(grid col rand cmd...) → gx gy gi"
                        "(let ([nume val] ...) cmd...)" "(seed N) → random reproductibil"))
               ,(cheat-col "Transform / Animatie"
                  (list "(group cmd...)" "(rotate grd cx cy cmd...)"
                        "(translate dx dy cmd...)" "(scale sx sy cmd...)"
                        "(opacity a cmd...)" "(spin cx cy sec cmd...)"
                        "(pulse sec cmd...)" "(blur px cmd...)"
                        "(glow culoare cmd...)" "(shadow dx dy px c cmd...)"
                        "(stroke c gros cmd...)" "(dash on off cmd...)"))
               ,(cheat-col "Numere"
                  (list "+  -  *  /  mod  pow" "sin cos tan atan atan2" "sqrt exp log abs sign"
                        "floor round ceil neg" "min max hypot dist" "(lerp a b t) (clamp x lo hi)"
                        "(map v il ih ol oh)" "(noise x y) → 0..1"
                        "(random max) (random lo hi)" "pi tau width height"))
               ,(cheat-col "Culori"
                  (list "#rrggbb" "nume-css (red...)" "(rgb r g b)" "(rgba r g b a)"
                        "(hsl h s l)" "(hsla h s l a)" "(hsv h s v)" "(mix c1 c2 t)"
                        "(palette \"nume\" i)" "fire ocean neon pastel sunset forest"
                        "(linear grd c1 c2 ...) ← umplere" "(radial c1 c2 ...) ← umplere"
                        "(linear-bg grd c1 c2 ...)" "(radial-bg c1 c2 ...)"))))
             ) ; /main

             (footer
              (p "Procedural Canvas DSL · scris in Racket cu web-server · "
                 (a ((href "https://github.com/Alexandru2984/racket") (target "_blank") (rel "noopener")) "cod sursa"))))
            (div ((id "toast") (class "toast") (role "status") (aria-live "polite")) "")
            (script ((src ,(string-append "/app.js?v=" APP-JS-VER)) (defer "defer"))))))])]))

;; The server only starts when this file is *run* (`racket app.rkt` executes the
;; `main` submodule).  Requiring the module — e.g. from the test submodule — runs
;; the definitions above without binding a socket, so the interpreter can be
;; exercised in isolation.
(module+ main
  ;; Open the gallery DB once up front so the first concurrent requests don't
  ;; race to create the connection (the feature degrades off if this fails).
  (void (gallery-db))
  (serve/servlet start
                 #:port PORT
                 #:listen-ip "127.0.0.1"
                 #:servlet-path "/"
                 #:servlet-regexp #rx""
                 #:command-line? #t))

;; ---------------------------------------------------------------------------
;; Regression tests for the resource caps.  Run with `raco test app.rkt`.
;; Each hostile input must (a) return in well under the hard time limit and
;; (b) produce a bounded number of SVG nodes — proving no single request can
;; exhaust CPU/RAM of the shared process.
;; ---------------------------------------------------------------------------
(module+ test
  (require rackunit)

  ;; Count every element node in a rendered xexpr tree.
  (define (count-nodes x)
    (cond [(and (pair? x) (symbol? (car x)))
           (+ 1 (for/sum ([c (in-list (cddr x))]) (count-nodes c)))]
          [(list? x) (for/sum ([c (in-list x)]) (count-nodes c))]
          [else 0]))

  (define (render-time text)
    (define t0 (current-inexact-milliseconds))
    (define svg (parse-to-svg text))
    (values svg (- (current-inexact-milliseconds) t0)))

  ;; Shared helper: a hostile payload must finish fast and stay bounded.
  ;; Returns void so nothing bubbles up and clutters the raco-test log.
  (define (check-bounded name text)
    (define-values (svg ms) (render-time text))
    (check-true (< ms 3500) (format "~a took ~ams (expected < 3500)" name ms))
    (check-true (< (count-nodes svg) 60000) (format "~a emitted too many nodes" name))
    (check-true (< (string-length (xexpr->string svg)) 2000000)
                (format "~a serialized output too large" name))
    (void))

  (test-case "valid art renders"
    (define svg (parse-to-svg "(bg \"#000\")(repeat 50 (circle (* i 10) 200 5 \"red\"))"))
    (check-eq? (car svg) 'svg)
    (check-true (> (count-nodes svg) 10)))

  (test-case "invalid commands in a big repeat are bounded (no budget bypass)"
    (check-bounded "invalid-cmd-flood"
      (string-append "(repeat 2000 " (apply string-append (make-list 3000 "(z)")) ")")))

  (test-case "empty let body with huge arithmetic is bounded (fuel cap)"
    (check-bounded "fuel-bomb"
      (string-append "(repeat 2000 (let ([a (+ " (apply string-append (make-list 20000 "1 ")) ")])))")))

  (test-case "polygon point amplification is bounded (point + output cap)"
    (define pts (apply string-append (make-list 600 "123.4 234.5 ")))
    (check-bounded "point-amplification"
      (string-append "(repeat 2000 (repeat 3 (polygon \"red\" " pts ")))")))

  (test-case "nested repeat multiplication is bounded"
    (check-bounded "nested-repeat"
      "(repeat 2000 (repeat 2000 (circle 1 1 1 \"red\")))"))

  (test-case "pow edge cases do not raise"
    (check-not-exn (lambda () (parse-to-svg "(circle (pow 0 -1) (pow -2 0.5) 5 \"red\")")))
    (check-not-exn (lambda () (parse-to-svg "(circle (pow 1e7 8) 1 1 \"red\")"))))

  (test-case "cyclic / reader payloads are rejected by the reader"
    (check-not-exn (lambda () (parse-to-svg "#0=(1 . #0#)")))
    (check-not-exn (lambda () (parse-to-svg "#lang racket"))))

  ;; --- DSL feature coverage --------------------------------------------------
  (define (svg->str x) (xexpr->string x))

  (test-case "value-noise is in [0,1] and smooth/deterministic"
    (for ([i (in-range 200)])
      (define v (value-noise (* i 0.37) (* i 0.11)))
      (check-true (and (>= v 0.0) (<= v 1.0))))
    (check-= (value-noise 3.5 2.25) (value-noise 3.5 2.25) 0.0))

  (test-case "new math ops evaluate"
    (check-not-exn (lambda ()
      (parse-to-svg "(circle (map i 0 10 0 600) (clamp (lerp 0 400 0.5) 0 400) (hypot 3 4) \"red\")"))))

  (test-case "mix produces a valid rgb() color"
    (define s (svg->str (parse-to-svg "(circle 1 1 1 (mix \"#ff0000\" \"#0000ff\" 0.5))")))
    (check-true (regexp-match? #px"rgb\\(12[78],0,12[78]\\)" s)))

  (test-case "gradients register a <defs> block"
    (define s (svg->str (parse-to-svg "(linear-bg 45 \"#000\" \"#fff\")(radial-bg \"red\" \"blue\")")))
    (check-true (regexp-match? #px"<defs>" s))
    (check-true (regexp-match? #px"linearGradient" s))
    (check-true (regexp-match? #px"radialGradient" s))
    (check-true (regexp-match? #px"url\\(#g" s)))

  (test-case "transforms wrap children in a <g transform=...>"
    (define s (svg->str (parse-to-svg "(rotate 30 300 200 (rect 0 0 10 10 \"red\"))")))
    (check-true (regexp-match? #px"<g transform=\"rotate\\(30 300 200\\)\">" s)))

  (test-case "animation emits SVG-native animate nodes (no JS)"
    (define s (svg->str (parse-to-svg "(spin 300 200 8 (rect 0 0 10 10 \"red\"))(pulse 2 (circle 1 1 1 \"red\"))")))
    (check-true (regexp-match? #px"animateTransform" s))
    (check-true (regexp-match? #px"<animate " s)))

  (test-case "seed makes randomness reproducible"
    (define a (svg->str (parse-to-svg "(seed 7)(repeat 20 (circle (random 600) (random 400) 3 \"red\"))")))
    (define b (svg->str (parse-to-svg "(seed 7)(repeat 20 (circle (random 600) (random 400) 3 \"red\"))")))
    (check-equal? a b)
    (define c (svg->str (parse-to-svg "(seed 8)(repeat 20 (circle (random 600) (random 400) 3 \"red\"))")))
    (check-not-equal? a c))

  (test-case "arc/ring/triangle render as expected shapes"
    (define s (svg->str (parse-to-svg "(arc 300 200 100 0 90 \"red\" 3)(ring 100 100 40 \"cyan\" 2)(triangle 0 0 10 0 5 10 \"lime\")")))
    (check-true (regexp-match? #px"<path" s))
    (check-true (regexp-match? #px"fill=\"none\"" s))
    (check-true (regexp-match? #px"<polygon" s)))

  ;; --- round 2: for / grid / poly / heart / hsv ------------------------------
  (test-case "for loop binds a named variable over a range, with optional step"
    (define a (svg->str (parse-to-svg "(for k 0 4 (circle k 0 1 \"red\"))")))
    (check-equal? (length (regexp-match* #px"<circle" a)) 5)
    (define b (svg->str (parse-to-svg "(for a 0 360 90 (circle a 0 1 \"red\"))")))
    (check-equal? (length (regexp-match* #px"<circle" b)) 5)) ; 0,90,180,270,360

  (test-case "for descending range iterates toward the end"
    (define s (svg->str (parse-to-svg "(for k 5 1 (circle k 0 1 \"red\"))")))
    (check-equal? (length (regexp-match* #px"<circle" s)) 5))

  (test-case "grid exposes gx/gy/gi and is bounded"
    (define s (svg->str (parse-to-svg "(grid 4 3 (circle gx gy gi \"red\"))")))
    (check-equal? (length (regexp-match* #px"<circle" s)) 12)
    ;; a huge grid is capped, not unbounded
    (check-not-exn (lambda () (parse-to-svg "(grid 200 200 (circle gx gy 1 \"red\"))"))))

  (test-case "poly and heart emit polygons; hsv yields rgb"
    (define s (svg->str (parse-to-svg "(poly 100 100 6 40 (hsv 200 80 90))(heart 300 200 30 \"red\")")))
    (check-equal? (length (regexp-match* #px"<polygon" s)) 2)
    (check-true (regexp-match? #px"rgb\\([0-9]+,[0-9]+,[0-9]+\\)" s)))

  (test-case "theme-independent: light palette CSS and toggle are present"
    (check-true (regexp-match? #px"data-theme=light" PAGE-CSS))
    (check-true (regexp-match? #px"btnTheme" PAGE-JS)))

  ;; --- round 3: palettes, effects, curve/spiral/sector -----------------------
  (test-case "palette returns a curated hex, unknown name falls back"
    (check-equal? (palette-color "fire" 0) "#2b0a00")
    (check-equal? (palette-color "fire" 6) "#2b0a00") ; wraps
    (check-equal? (palette-color "nope" 0) "#888888")
    (define s (svg->str (parse-to-svg "(circle 1 1 1 (palette \"neon\" 2))")))
    (check-true (regexp-match? #px"#[0-9a-fA-F]{6}" s)))

  (test-case "effects register SVG filters and wrap children (no JS)"
    (define s (svg->str (parse-to-svg "(blur 3 (circle 1 1 1 \"red\"))(glow \"cyan\" (circle 2 2 2 \"red\"))(shadow 2 2 2 \"black\" (rect 0 0 5 5 \"red\"))")))
    (check-true (regexp-match? #px"<filter" s))
    (check-true (regexp-match? #px"feGaussianBlur" s))
    (check-true (regexp-match? #px"feDropShadow" s))
    (check-true (regexp-match? #px"filter=\"url\\(#" s)))

  (test-case "curve/spiral/sector emit paths and are bounded"
    (define s (svg->str (parse-to-svg "(curve \"red\" 2 0 0 50 50 100 0 150 50)(spiral 300 200 5 2 100 \"cyan\" 2)(sector 300 200 100 0 90 \"lime\")")))
    (check-equal? (length (regexp-match* #px"<path" s)) 3)
    (check-not-exn (lambda () (parse-to-svg "(spiral 300 200 30 0 1000 \"red\" 2)"))))

  (test-case "effect filters still obey the element budget"
    (define svg (parse-to-svg (string-append "(repeat 9000 (glow \"red\" (circle 1 1 1 \"red\")))")))
    (check-true (< (count-nodes svg) 60000)))

  ;; --- round 4: pro editor assets are wired into the page --------------------
  (test-case "pro editor markup, styles and script are present"
    (check-true (regexp-match? #px"editor-wrap" PAGE-CSS))
    (check-true (regexp-match? #px"tk-cmd" PAGE-CSS))
    (check-true (regexp-match? #px"\\.errbar" PAGE-CSS))
    (check-true (regexp-match? #px"function highlight" PAGE-JS))
    (check-true (regexp-match? #px"hl-on" PAGE-JS))
    (check-true (regexp-match? #px"showErrors" PAGE-JS)))

  ;; --- round 6: gallery helpers --------------------------------------------
  (test-case "share encode/decode round-trips (incl. non-ASCII)"
    (define src "(bg \"#0b0f1a\") ;; vârtej cu diacritice\n(circle 1 1 1 \"red\")")
    ;; encode-share percent-encodes +,/,=; the server URL-decodes before decode-share
    (define enc (encode-share src))
    (define url-decoded (regexp-replaces enc '((#rx"%2B" "+") (#rx"%2F" "/") (#rx"%3D" "="))))
    (check-equal? (decode-share url-decoded) src))

  (test-case "sanitize-title trims, caps length and strips control chars"
    (check-equal? (sanitize-title "   ") "fara titlu")
    (check-equal? (sanitize-title "") "fara titlu")
    (check-equal? (sanitize-title "  hello  world  ") "hello world")
    (check-equal? (sanitize-title (string-append "x\u0000\u0007y")) "x y")
    (check-true (<= (string-length (sanitize-title (make-string 200 #\a))) MAX-TITLE)))

  (test-case "gallery card escapes the title and links the thumbnail"
    (define s (xexpr->string (gallery-card (vector 7 "<b>hax</b>" "(circle 1 1 1 \"red\")"))))
    (check-true (regexp-match? #px"/thumb/7" s))
    (check-true (regexp-match? #px"&lt;b&gt;hax" s))   ; escaped, not raw markup
    (check-false (regexp-match? #px"<b>hax</b>" s))
    (check-true (regexp-match? #px"/\\?c=" s)))        ; open-in-editor permalink

  ;; --- round 7: per-shape gradients, stroke/dash ----------------------------
  (test-case "linear/radial color builders register gradients and dedup"
    (define a (xexpr->string (parse-to-svg "(repeat 10 (circle (* i 40) 200 30 (linear 45 \"#f00\" \"#00f\")))")))
    (check-true (regexp-match? #px"linearGradient" a))
    (check-true (regexp-match? #px"fill=\"url\\(#" a))
    ;; one gradient reused for all ten identical fills
    (check-equal? (length (regexp-match* #px"<linearGradient" a)) 1)
    (define b (xexpr->string (parse-to-svg "(circle 1 1 1 (radial \"#fff\" \"#000\"))")))
    (check-true (regexp-match? #px"radialGradient" b)))

  (test-case "varying per-shape gradients are not wrongly deduped"
    (define s (xexpr->string (parse-to-svg "(repeat 5 (circle (* i 40) 200 30 (radial (hsl (* i 60) 80 60) \"#000\")))")))
    (check-equal? (length (regexp-match* #px"<radialGradient" s)) 5))

  (test-case "stroke and dash wrap children via group inheritance"
    (define s (xexpr->string (parse-to-svg "(stroke \"#fff\" 3 (circle 1 1 1 \"none\"))(dash 8 6 (line 0 0 9 9 \"red\" 2))")))
    (check-true (regexp-match? #px"stroke=\"#fff\"" s))
    (check-true (regexp-match? #px"stroke-dasharray=\"8,6\"" s)))

  (test-case "gradient fills still obey the element/defs budget"
    (define svg (parse-to-svg "(repeat 9000 (circle 1 1 1 (radial (hsl i 80 60) \"#000\")))"))
    (check-true (< (count-nodes svg) 70000)))

  ;; --- round 8: gallery likes (DB integration; skipped if DB unavailable) ---
  (test-case "likes dedup per IP and drive the popular sort"
    (when (gallery-db)
      (define art "(bg \"#000\")(circle 1 1 1 \"red\")(circle 2 2 2 \"blue\")")
      ;; unique IPs avoid the per-IP save cooldown
      (define ip1 (format "t~a-1" (current-milliseconds)))
      (define ip2 (format "t~a-2" (current-milliseconds)))
      (define-values (ok1 _m1) (gallery-save! "likeobj-A" art ip1))
      (define-values (ok2 _m2) (gallery-save! "likeobj-B" art ip2))
      (check-true (and ok1 ok2))
      ;; newest two rows are ours (B then A)
      (define rows (gallery-list #f 'recent))
      (define idB (vector-ref (car rows) 0))
      (define idA (vector-ref (cadr rows) 0))
      ;; like A from two voters; a repeat from the same voter is rejected
      (check-equal? (gallery-like! idA "voter-x") 1)
      (check-equal? (gallery-like! idA "voter-y") 2)
      (check-false (gallery-like! idA "voter-x"))      ; dedup
      (check-false (gallery-like! 999999999 "voter-z")) ; missing id
      ;; A (2 likes) now outranks B (0) in the popular view
      (define pop (gallery-list #f 'popular))
      (check-equal? (vector-ref (car pop) 0) idA))))
