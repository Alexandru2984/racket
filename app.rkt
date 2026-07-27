#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/http/bindings
         net/url
         racket/draw
         racket/math
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
;; unknown form evaluates to 0 rather than raising.
(define (eval-num v env [depth 0])
  (define (ev x) (eval-num x env (add1 depth)))
  (cond
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
                                       (if (and (<= base 0) (not (integer? e))) 0 (expt base e)))]
        [(list 'sin a)               (sin (ev a))]
        [(list 'cos a)               (cos (ev a))]
        [(list 'tan a)               (let ([c (cos (ev a))]) (if (zero? c) 0 (/ (sin (ev a)) c)))]
        [(list 'sqrt a)              (let ([x (ev a)]) (if (< x 0) 0 (sqrt x)))]
        [(list 'abs a)               (abs (ev a))]
        [(list 'neg a)               (- (ev a))]
        [(list 'floor a)             (floor (ev a))]
        [(list 'round a)             (round (ev a))]
        [(cons 'min (and args (cons _ _))) (apply min (map ev args))]
        [(cons 'max (and args (cons _ _))) (apply max (map ev args))]
        [_ 0]))]
    [else 0]))

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
    [_ fallback]))

;; ---------------------------------------------------------------------------
;; Render context: a shared, mutable budget so total emitted nodes are capped
;; regardless of how the commands are nested.
;; ---------------------------------------------------------------------------
(struct rctx (budget) #:mutable)
(define (make-rctx) (rctx MAX-ELEMENTS))
(define (budget-left? ctx) (> (rctx-budget ctx) 0))
(define (spend! ctx) (set-rctx-budget! ctx (sub1 (rctx-budget ctx))))

(define (short-str s)
  (define str (format "~a" s))
  (if (> (string-length str) 200) (string-append (substring str 0 200) "…") str))

(define (err-node label msg y)
  (list `(text ((x "12") (y ,(number->string y)) (fill "#ff5555")
                (font-family "monospace") (font-size "13"))
               ,(string-append label ": " (short-str msg)))))

;; Cap text length so a single (text ...) node can't carry a megabyte of glyphs.
(define MAX-TEXT-LEN 300)
(define (clip-text s)
  (if (> (string-length s) MAX-TEXT-LEN) (substring s 0 MAX-TEXT-LEN) s))

;; Turn a flat list of coordinate expressions into an SVG "x,y x,y ..." string.
;; Points are capped so a giant coordinate list can't bloat one element.
(define MAX-POINTS 600)
(define (points->str exprs env)
  (define nums (for/list ([e (in-list exprs)] [_ (in-range (* 2 MAX-POINTS))])
                 (eval-num e env)))
  (let loop ([xs nums] [acc '()])
    (cond
      [(or (null? xs) (null? (cdr xs))) (string-join (reverse acc) " ")]
      [else (loop (cddr xs) (cons (format "~a,~a" (fmt-num (car xs)) (fmt-num (cadr xs))) acc))])))

;; Build a star / n-gon burst as a <polygon>.  Spike count is clamped.
(define (star-xexpr cx cy spikes outer inner fill)
  (define n (max 2 (min 100 (inexact->exact (floor spikes)))))
  (define pts
    (for/list ([k (in-range (* 2 n))])
      (define r (if (even? k) outer inner))
      (define ang (- (* k (/ pi n)) (/ pi 2)))
      (format "~a,~a" (fmt-num (+ cx (* r (cos ang)))) (fmt-num (+ cy (* r (sin ang)))))))
  `(polygon ((points ,(string-join pts " ")) (fill ,fill)) ""))

;; Interpret one command into a list of SVG xexprs.  `env` carries constants /
;; the loop index / locals, `depth` bounds nesting, `ctx` bounds total output.
;; Every path is guarded so malformed or hostile input degrades to a small
;; error node instead of an exception/hang.
(define (interpret cmd env ctx depth)
  (cond
    [(not (budget-left? ctx)) '()]
    [(> depth MAX-DEPTH) '()]
    [else
     (with-handlers ([exn:fail? (lambda (e) (err-node "Eroare interpretare" (exn-message e) 24))])
       (define (n v) (fmt-num (eval-num v env)))
       (define (col c) (eval-color c env))
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
                 (for/list ([i (in-range reps)] #:break (not (budget-left? ctx)))
                   (define env* (hash-set env 'i i))
                   (apply append
                          (for/list ([b (in-list body)]) (interpret b env* ctx (add1 depth))))))]
         [_ (err-node "Comanda invalida" (short-str cmd) 40)]))]))

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
  (define elements
    (if (list? forms)
        (apply append
               (for/list ([c (in-list forms)] #:break (not (budget-left? ctx)))
                 (interpret c BASE-ENV ctx 0)))
        '()))
  (define notice
    (if (<= (rctx-budget ctx) 0)
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
        ,@elements ,@notice))

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

(define DEFAULT-CODE
  (string-append
   ";; Foloseste (i) = indexul buclei, trigonometrie si culori hsl calculate.\n"
   "(bg \"#0b0f1a\")\n\n"
   ";; Un vartej de cercuri colorate\n"
   "(repeat 90\n"
   "  (circle (+ 300 (* (* i 2.2) (cos (* i 0.35))))\n"
   "          (+ 200 (* (* i 2.2) (sin (* i 0.35))))\n"
   "          6\n"
   "          (hsl (* i 5) 85 60)))\n\n"
   ";; O stea in centru\n"
   "(star 300 200 5 40 16 \"#f1fa8c\")"))

;; ---------------------------------------------------------------------------
;; UI: mobile-first responsive page.  The app is server-rendered and fully
;; usable without JavaScript (examples are plain POST forms); JS only adds the
;; copy-to-clipboard convenience and the chosen-file name.
;; ---------------------------------------------------------------------------
(define PAGE-CSS "
:root{--bg:#0b0d14;--bg2:#0f121b;--panel:#161a26;--panel2:#1b2030;--border:#272d40;
--border2:#333b52;--text:#e7e9f3;--muted:#9aa3bd;--purple:#bd93f9;--pink:#ff79c6;
--cyan:#8be9fd;--green:#50fa7b;--yellow:#f1fa8c;--radius:14px}
*{box-sizing:border-box}html{-webkit-text-size-adjust:100%}
body{margin:0;font-family:system-ui,-apple-system,Roboto,Arial,sans-serif;color:var(--text);
line-height:1.55;min-height:100vh;background:
radial-gradient(1100px 560px at 82% -12%,#1a1030 0,transparent 60%),
radial-gradient(950px 480px at -8% 8%,#08202b 0,transparent 55%),var(--bg)}
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
@media(min-width:920px){.grid{grid-template-columns:minmax(0,1fr) minmax(0,1fr);align-items:start}}
.panel{background:linear-gradient(180deg,var(--panel),var(--bg2));border:1px solid var(--border);
border-radius:var(--radius);padding:clamp(.9rem,2.5vw,1.25rem);box-shadow:0 12px 30px rgba(0,0,0,.35)}
.panel h2{font-size:.82rem;margin:0 0 .7rem;color:var(--muted);text-transform:uppercase;letter-spacing:.07em}
textarea{width:100%;min-height:340px;resize:vertical;background:#0b0e17;color:#f5f6ff;
border:1px solid var(--border);border-radius:10px;padding:1rem;tab-size:2;
font:15px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
textarea:focus,input:focus,button:focus-visible,.btn:focus-visible{outline:2px solid var(--purple);outline-offset:2px}
.toolbar{display:flex;flex-wrap:wrap;gap:.55rem;margin-top:.8rem}
button,.btn{font:600 15px/1 system-ui,sans-serif;cursor:pointer;border:none;border-radius:10px;
padding:.75rem 1.1rem;color:#12131a;background:var(--purple);display:inline-flex;align-items:center;
gap:.4rem;transition:filter .15s,transform .05s}
button:hover,.btn:hover{filter:brightness(1.08);text-decoration:none}
button:active,.btn:active{transform:translateY(1px)}
.btn-ghost{background:transparent;color:var(--text);border:1px solid var(--border2)}
.btn-cyan{background:var(--cyan)}.btn-pink{background:var(--pink)}
.stage{background:#000;border:1px solid var(--border);border-radius:var(--radius);padding:.55rem;overflow:hidden}
.stage svg{width:100%;height:auto;display:block}
.hint{color:var(--muted);font-size:.85rem;margin:.55rem 0 0}
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
@media(min-width:1000px){.cheat-grid{grid-template-columns:repeat(4,1fr)}}
.cheat-grid h3{color:var(--cyan);font-size:.78rem;text-transform:uppercase;letter-spacing:.05em;margin:.1rem 0 .5rem}
.cheat-grid ul{list-style:none;margin:0;padding:0}.cheat-grid li{margin:.35rem 0}
code{background:#0b0e17;border:1px solid var(--border);padding:.14rem .42rem;border-radius:6px;
font:12.5px ui-monospace,Menlo,monospace;color:var(--green);white-space:nowrap}
footer{text-align:center;color:var(--muted);font-size:.85rem;margin-top:2rem;padding-top:1rem;border-top:1px solid var(--border)}
.toast{position:fixed;left:50%;bottom:1.2rem;transform:translateX(-50%) translateY(150%);background:var(--panel2);
border:1px solid var(--border2);color:var(--text);padding:.7rem 1.1rem;border-radius:10px;
box-shadow:0 10px 30px rgba(0,0,0,.4);transition:transform .25s;z-index:50}
.toast.show{transform:translateX(-50%) translateY(0)}
@media(prefers-reduced-motion:reduce){*{transition:none!important}}
")

;; Kept free of & < > so it survives xexpr's pcdata escaping unchanged.
(define PAGE-JS "
(function(){
  var ta=document.getElementById('code');
  function toast(m){var t=document.getElementById('toast');if(!t){return;}
    t.textContent=m;t.classList.add('show');clearTimeout(window.__tt);
    window.__tt=setTimeout(function(){t.classList.remove('show');},1800);}
  function fallback(){if(!ta){return;}ta.focus();ta.select();try{document.execCommand('copy');}catch(e){}toast('Cod copiat');}
  function copyCode(){if(!ta){return;}
    if(navigator.clipboard){navigator.clipboard.writeText(ta.value).then(function(){toast('Cod copiat');},fallback);}
    else{fallback();}}
  var b=document.getElementById('btnCopy');if(b){b.addEventListener('click',copyCode);}
  var f=document.getElementById('image_file');
  if(f){f.addEventListener('change',function(){var n=document.getElementById('fname');
    if(n){n.textContent=f.files[0]?f.files[0].name:'';}});}
})();
")

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
         "(bg \"#0b0f1a\")\n(repeat 60\n  (circle (* i 10) (+ 200 (* 120 (sin (* i 0.3)))) 6 (hsl (* i 6) 85 60)))")))

(define (example-card title desc code)
  `(form ((method "post") (class "ex-form"))
     (input ((type "hidden") (name "action") (value "preview")))
     (input ((type "hidden") (name "code") (value ,code)))
     (button ((type "submit") (class "ex")) ,title (small ,desc))))

(define (cheat-col heading items)
  `(div (h3 ,heading)
        (ul ,@(for/list ([it (in-list items)]) `(li (code ,it))))))

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
         [else code-val]))

     (define final-code
       (if (non-empty-string? initial-code) initial-code DEFAULT-CODE))

     (cond
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
            (title "Procedural Canvas DSL — Racket")
            (meta ((name "viewport") (content "width=device-width, initial-scale=1")))
            (meta ((name "color-scheme") (content "dark")))
            (meta ((name "description")
                   (content "Un mic limbaj Lisp-like scris in Racket care randeaza arta SVG: bucle, trigonometrie, culori si forme procedurale.")))
            (link ((rel "icon")
                   (href "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect width='32' height='32' rx='7' fill='%230b0d14'/%3E%3Ccircle cx='16' cy='16' r='9' fill='%23bd93f9'/%3E%3C/svg%3E")))
            (style ,PAGE-CSS))
           (body
            (div ((class "wrap"))
             (header ((class "hero"))
              (div ((class "badge")) "Racket · web-server · SVG")
              (h1 "Procedural Canvas DSL")
              (p "Scrie cod, obtii arta. Bucle, trigonometrie, culori si forme — totul randat pe server, apoi descarcabil ca SVG."))

             (div ((class "grid"))
              (section ((class "panel"))
               (h2 "Editor")
               (form ((method "post"))
                (textarea ((id "code") (name "code") (spellcheck "false")
                           (autocomplete "off") (autocapitalize "off") (autocorrect "off")
                           (placeholder "Codul tau aici...")) ,final-code)
                (div ((class "toolbar"))
                 (button ((type "submit") (name "action") (value "preview")) "▶ Randeaza")
                 (button ((type "submit") (name "action") (value "download") (class "btn-cyan")) "⭳ Download SVG")
                 (button ((type "button") (id "btnCopy") (class "btn-ghost")) "⧉ Copiaza")
                 (a ((href "/") (class "btn btn-ghost")) "↺ Reset")))
               (p ((class "hint")) "Sfat: in (repeat N ...) variabila (i) e indexul iteratiei. Referinta completa mai jos."))

              (section ((class "panel"))
               (h2 "Panza (600 × 400)")
               (div ((class "stage")) ,(parse-to-svg final-code))
               (h2 ((style "margin-top:1.15rem")) "Imagine → cod DSL")
               (form ((method "post") (enctype "multipart/form-data") (class "file-row"))
                (input ((type "hidden") (name "action") (value "upload")))
                (input ((type "file") (id "image_file") (name "image_file") (accept "image/png,image/jpeg")))
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
                        "(polygon culoare x1 y1 ...)" "(polyline culoare gros x1 y1 ...)"
                        "(star cx cy varfuri rext rint culoare)"
                        "(text x y marime culoare STR)" "(bg culoare)"))
               ,(cheat-col "Control"
                  (list "(repeat N cmd...)" "i = index in repeat"
                        "(let ([nume val] ...) cmd...)"))
               ,(cheat-col "Numere"
                  (list "+  -  *  /  mod  pow" "sin cos tan sqrt" "abs neg floor round"
                        "min max" "(random max)" "(random lo hi)" "pi tau width height"))
               ,(cheat-col "Culori"
                  (list "#rrggbb" "nume-css (red...)" "(rgb r g b)" "(rgba r g b a)"
                        "(hsl h s l)" "(hsla h s l a)"))))

             (footer
              (p "Procedural Canvas DSL · scris in Racket cu web-server · "
                 (a ((href "https://github.com/Alexandru2984/racket") (target "_blank") (rel "noopener")) "cod sursa"))))
            (div ((id "toast") (class "toast")) "")
            (script ,PAGE-JS))))])]))

(serve/servlet start
               #:port PORT
               #:listen-ip "127.0.0.1"
               #:servlet-path "/"
               #:servlet-regexp #rx""
               #:command-line? #t)
