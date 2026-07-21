#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/http/bindings
         racket/draw
         xml)

(define (eval-val v)
  (with-handlers ([exn:fail? (lambda (e) 0)])
    (match v
      [(? number?) v]
      [(? string?) v]
      [(list 'random n) 
       (let ([max-val (inexact->exact (floor (eval-val n)))])
         (if (<= max-val 0) 0 (random max-val)))]
      [(list '+ a b) (+ (eval-val a) (eval-val b))]
      [(list '- a b) (- (eval-val a) (eval-val b))]
      [(list '* a b) (* (eval-val a) (eval-val b))]
      [(list '/ a b) (let ([denom (eval-val b)]) (if (= denom 0) 0 (/ (eval-val a) denom)))]
      [_ v])))

(define (interpret-cmd cmd)
  (with-handlers ([exn:fail? (lambda (e) 
     (list `(text ((x "10") (y "20") (fill "#ff5555")) ,(string-append "Eroare interpretare: " (exn-message e)))))])
    (match cmd
      [(list 'circle cx cy r c)
       (list `(circle ((cx ,(number->string (eval-val cx)))
                       (cy ,(number->string (eval-val cy)))
                       (r ,(number->string (eval-val r)))
                       (fill ,(eval-val c))) ""))]
      [(list 'rect x y w h c)
       (list `(rect ((x ,(number->string (eval-val x)))
                     (y ,(number->string (eval-val y)))
                     (width ,(number->string (eval-val w)))
                     (height ,(number->string (eval-val h)))
                     (fill ,(eval-val c))) ""))]
      [(list 'line x1 y1 x2 y2 c w)
       (list `(line ((x1 ,(number->string (eval-val x1)))
                     (y1 ,(number->string (eval-val y1)))
                     (x2 ,(number->string (eval-val x2)))
                     (y2 ,(number->string (eval-val y2)))
                     (stroke ,(eval-val c))
                     (stroke-width ,(number->string (eval-val w))))))]
      [(list 'repeat n cmds ...)
       (apply append (for/list ([i (eval-val n)])
                       (apply append (map interpret-cmd cmds))))]
      [_ (list `(text ((x "10") (y "40") (fill "#ff5555")) ,(string-append "Comanda invalida: " (format "~a" cmd))))])))

(define (parse-to-svg text)
  (define in (open-input-string (string-append "(" text ")")))
  (define cmds (with-handlers ([exn:fail:read? (lambda (e) '())]) (read in)))
  (define elements (if (list? cmds) (apply append (map interpret-cmd cmds)) '()))
  `(svg ((xmlns "http://www.w3.org/2000/svg")
         (width "600") (height "400")
         (style "border: 1px solid #444; background: #000; border-radius: 8px;"))
        ,@elements))

(define (image->dsl bytes-data)
  (with-handlers ([exn:fail? (lambda (e) (string-append ";; Eroare procesare imagine: " (exn-message e)))])
    (define bmp (make-object bitmap% (open-input-bytes bytes-data)))
    (if (not (send bmp ok?))
        ";; Eroare: Fisierul nu este o imagine valida (JPG/PNG)."
        (let* ([w (send bmp get-width)]
               [h (send bmp get-height)]
               [target-w 60]
               [target-h (max 1 (inexact->exact (round (* target-w (/ h w)))))]
               [scaled-bmp (make-object bitmap% target-w target-h)])
          (define dc (make-object bitmap-dc% scaled-bmp))
          (send dc set-smoothing 'smoothed)
          (send dc set-scale (/ target-w w) (/ target-h h))
          (send dc draw-bitmap bmp 0 0)
          (define pixels (make-bytes (* target-w target-h 4)))
          (send scaled-bmp get-argb-pixels 0 0 target-w target-h pixels)
          
          (define out (open-output-string))
          (fprintf out ";; Imagine convertita automat in cod procedură (rezolutie ~ax~a)\n" target-w target-h)
          (for* ([y target-h] [x target-w])
            (define idx (* 4 (+ (* y target-w) x)))
            (define a (bytes-ref pixels idx))
            (define r (bytes-ref pixels (+ idx 1)))
            (define g (bytes-ref pixels (+ idx 2)))
            (define b (bytes-ref pixels (+ idx 3)))
            (when (> a 10)
              (fprintf out "(circle ~a ~a 4 \"rgb(~a,~a,~a)\")\n" 
                       (inexact->exact (round (* x (/ 600 target-w))))
                       (inexact->exact (round (* y (/ 400 target-h))))
                       r g b)))
          (get-output-string out)))))

(define (start req)
  (define bindings (request-bindings/raw req))
  
  (define (extract-form-value key)
    (define b (bindings-assq key bindings))
    (if (and b (binding:form? b)) (bytes->string/utf-8 (binding:form-value b)) ""))
    
  (define (extract-file-content key)
    (define b (bindings-assq key bindings))
    (if (and b (binding:file? b)) (binding:file-content b) #f))
    
  (define action (extract-form-value #"action"))
  (define code-val (extract-form-value #"code"))
  (define uploaded-file (extract-file-content #"image_file"))
  
  (define initial-code
    (cond
      [(equal? action "upload")
       (if (and uploaded-file (bytes? uploaded-file) (> (bytes-length uploaded-file) 0))
           (image->dsl uploaded-file)
           ";; Eroare la incarcarea fisierului")]
      [else code-val]))
      
  (define final-code
    (if (non-empty-string? initial-code)
        initial-code
        ";; Magie cu bucle (repeat) si functii (random)\n(repeat 80\n  (circle (random 600) (random 400) (random 40) \"rgba(255, 121, 198, 0.5)\"))\n\n;; Un patrat cu matematica simpla\n(rect (+ 100 100) (/ 400 2) 200 50 \"#8be9fd\")"))

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
          
          ,(parse-to-svg final-code)))))]))

(serve/servlet start
               #:port 8345
               #:listen-ip "127.0.0.1"
               #:servlet-path "/"
               #:command-line? #t)
