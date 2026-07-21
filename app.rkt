#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/http/bindings
         net/url
         racket/draw
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

;; Safe numeric evaluator for the little arithmetic sub-language.  Bounded in
;; both recursion depth and value magnitude; unknown forms evaluate to 0.
(define (eval-num v [depth 0])
  (cond
    [(> depth MAX-EXPR-DEPTH) 0]
    [(number? v) (clamp-num (if (real? v) v 0))]
    [(pair? v)
     (clamp-num
      (match v
        [(list 'random n)
         (let ([m (inexact->exact (floor (max 0 (eval-num n (add1 depth)))))])
           (if (<= m 0) 0 (random (min m MAX-RANDOM))))]
        [(list '+ a b) (+ (eval-num a (add1 depth)) (eval-num b (add1 depth)))]
        [(list '- a b) (- (eval-num a (add1 depth)) (eval-num b (add1 depth)))]
        [(list '* a b) (* (eval-num a (add1 depth)) (eval-num b (add1 depth)))]
        [(list '/ a b) (let ([d (eval-num b (add1 depth))])
                         (if (zero? d) 0 (/ (eval-num a (add1 depth)) d)))]
        [_ 0]))]
    [else 0]))

;; ---------------------------------------------------------------------------
;; Colors — validated against a conservative whitelist.  xexpr->string already
;; escapes attribute values (so this is not the XSS boundary), but rejecting
;; junk keeps the SVG well-formed and blocks any attribute-context surprises.
;; ---------------------------------------------------------------------------
(define color-rx
  #px"^(#[0-9a-fA-F]{3,8}|rgba?\\([-0-9.,%[:space:]]+\\)|hsla?\\([-0-9.,%[:space:]]+\\)|[a-zA-Z]{1,20})$")

(define (eval-color c [fallback "#ff79c6"])
  (define s (and (string? c) (string-trim c)))
  (if (and s (<= (string-length s) 40) (regexp-match? color-rx s)) s fallback))

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

;; Interpret one command into a list of SVG xexprs.  `depth` bounds nesting;
;; the context bounds total output.  Every path is guarded so malformed or
;; hostile input degrades to a small error node instead of an exception/hang.
(define (interpret cmd ctx depth)
  (cond
    [(not (budget-left? ctx)) '()]
    [(> depth MAX-DEPTH) '()]
    [else
     (with-handlers ([exn:fail? (lambda (e) (err-node "Eroare interpretare" (exn-message e) 24))])
       (match cmd
         [(list 'circle cx cy r c)
          (spend! ctx)
          (list `(circle ((cx ,(fmt-num (eval-num cx))) (cy ,(fmt-num (eval-num cy)))
                          (r ,(fmt-num (eval-num r))) (fill ,(eval-color c))) ""))]
         [(list 'rect x y w h c)
          (spend! ctx)
          (list `(rect ((x ,(fmt-num (eval-num x))) (y ,(fmt-num (eval-num y)))
                        (width ,(fmt-num (eval-num w))) (height ,(fmt-num (eval-num h)))
                        (fill ,(eval-color c))) ""))]
         [(list 'line x1 y1 x2 y2 c w)
          (spend! ctx)
          (list `(line ((x1 ,(fmt-num (eval-num x1))) (y1 ,(fmt-num (eval-num y1)))
                        (x2 ,(fmt-num (eval-num x2))) (y2 ,(fmt-num (eval-num y2)))
                        (stroke ,(eval-color c)) (stroke-width ,(fmt-num (eval-num w)))) ""))]
         [(list 'repeat n cmds ...)
          (spend! ctx)
          (define reps (min MAX-REPEAT (max 0 (inexact->exact (floor (eval-num n))))))
          (apply append
                 (for/list ([_ (in-range reps)] #:break (not (budget-left? ctx)))
                   (apply append
                          (for/list ([c (in-list cmds)]) (interpret c ctx (add1 depth))))))]
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
                 (interpret c ctx 0)))
        '()))
  (define notice
    (if (<= (rctx-budget ctx) 0)
        (list `(text ((x "12") (y "392") (fill "#ffb86c") (font-family "monospace") (font-size "12"))
                     "… limita de complexitate atinsa (output trunchiat)"))
        '()))
  `(svg ((xmlns "http://www.w3.org/2000/svg")
         (width "600") (height "400")
         (style "border: 1px solid #444; background: #000; border-radius: 8px;"))
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
   ";; Magie cu bucle (repeat) si functii (random)\n"
   "(repeat 80\n"
   "  (circle (random 600) (random 400) (random 40) \"rgba(255, 121, 198, 0.5)\"))\n\n"
   ";; Un patrat cu matematica simpla\n"
   "(rect (+ 100 100) (/ 400 2) 200 50 \"#8be9fd\")"))

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
         `(html
           (head (title "Procedural DSL Art")
                 (meta ((name "viewport") (content "width=device-width, initial-scale=1.0")))
                 (style "body { font-family: system-ui, sans-serif; display: flex; flex-direction: column; align-items: center; padding: 2rem; background: #111; color: #eee; } textarea { background: #222; color: #ff79c6; border: 1px solid #444; padding: 1rem; width: 600px; height: 300px; font-size: 16px; font-family: monospace; border-radius: 4px; margin-bottom: 1rem; } button { padding: 0.8rem 1.5rem; font-size: 16px; cursor: pointer; background: #bd93f9; color: #282a36; font-weight: bold; border: none; border-radius: 4px; margin: 0.5rem; } button:hover { background: #ff79c6; } svg { margin-top: 1rem; box-shadow: 0 10px 30px rgba(0,0,0,0.5); } .container { max-width: 800px; text-align: center; } p { color: #8be9fd; } code { background: #282a36; padding: 2px 6px; border-radius: 4px; } .panel { background: #222; padding: 1rem; border-radius: 8px; margin-bottom: 1rem; border: 1px solid #444; }"))
           (body
            (div ((class "container"))
             (h1 "Procedural Canvas DSL (Racket)")

             (div ((class "panel"))
              (p (strong "Nou!") " Acum poti folosi bucle si functii.")
              (p (code "(repeat N comenzi...)") " " (code "(random MAX)") " " (code "(+ a b)"))
              (p "Incarca o imagine (JPG/PNG) pentru a genera codul ei in DSL:")
              (form ((method "POST") (enctype "multipart/form-data"))
                    (input ((type "hidden") (name "action") (value "upload")))
                    (input ((type "file") (name "image_file") (accept "image/png, image/jpeg")))
                    (button ((type "submit")) "Converteste Imagine in Cod")))

             (form ((method "POST"))
                   (textarea ((name "code") (placeholder "Codul tau aici...")) ,final-code)
                   (br)
                   (button ((type "submit") (name "action") (value "preview")) "Pre-vizualizare")
                   (button ((type "submit") (name "action") (value "download")) "Download SVG"))

             ,(parse-to-svg final-code)))))])]))

(serve/servlet start
               #:port PORT
               #:listen-ip "127.0.0.1"
               #:servlet-path "/"
               #:servlet-regexp #rx""
               #:command-line? #t)
