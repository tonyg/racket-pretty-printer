#lang racket/base
;; A Racket library based on Philip Wadler's presentation of a pretty
;; printing algorithm [1], "A prettier printer", 2003. PDF available [2].
;;
;; [1] http://homepages.inf.ed.ac.uk/wadler/topics/language-design.html#prettier
;; [2] http://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

(provide <>
         nest
         group
         flatten
         pretty-print
         pretty-print->string

         <?>
         <+>
         </>
         folddoc

         spread
         stack
         <>*
         <>**

         cbracket

         <+/>
         fillwords
         fill

         sbracket)

(require racket/match)
(require (only-in racket/port call-with-output-string))
(require (only-in racket/promise delay force))
(require (only-in racket/string string-split string-append*))
(module+ test (require rackunit))

;;---------------------------------------------------------------------------
;; Core

;; Wadler's DOC type
;; NIL is represented by the empty string, collapsing it into the TEXT case
;; TEXT is represented by just the string itself
;; LINE is represented by 'line
(struct <> (l r) #:prefab)
(struct nest (i d) #:prefab)
(struct -alt (first second) #:prefab) ;; not for user exposure

;; Invariants on -alt instances:
;;  - all layouts in `first` and `second` must `flatten` to the same layout
;;  - no first line of `first` is shorter than any first line in `second`

;; Wadler's Doc = `(U '() (Consof (U String Natural) (Promiseof Doc)))`,
;; where the `String`s are the `Text` instances, and the `Natural`s
;; are the `Line` instances. The thunking is for necessary laziness.

;; DOC -> DOC
(define (group x)
  (-alt (flatten x) (lambda () x)))

;; DOC -> DOC
(define (flatten x)
  (match x
    [(<> l r)      (<> (flatten l) (flatten r))]
    [(nest i d)    (nest i (flatten d))]
    [(? string? s) s]
    ['line         " "]
    [(-alt a b)    (flatten a)])) ;; by invariant

;; OutputPort Doc -> Void
(define (layout p x)
  (let walk ((x x))
    (match x
      ['() '()]
      [(cons e more)
       (match e
         [(? string? s)
          (write-string s p)]
         [(? integer? i)
          (write-char #\newline p)
          (for [(n (in-range i))] (write-char #\space p))])
       (walk (force more))])))

;; Natural Natural DOC -> Doc
;; Best layout for `x` in the remaining `available` columns after
;; `used` columns have been printed on.
(define (best available used x)
  (let be ((w available) (k used) (chunks (list (cons 0 x))))
    (match chunks
      ['()                              '()]
      [(cons (cons i (<> l r)) cs)      (be w k (list* (cons i l) (cons i r) cs))]
      [(cons (cons i (nest j d)) cs)    (be w k (cons (cons (+ i j) d) cs))]
      [(cons (cons i (? string? s)) cs) (cons s (delay (be w (+ k (string-length s)) cs)))]
      [(cons (cons i 'line) cs)         (cons i (delay (be w i cs)))]
      [(cons (cons i (-alt a b)) cs)    (better w
                                                k
                                                (be w k (cons (cons i a) cs))
                                                (lambda ()
                                                  (be w k (cons (cons i (b)) cs))))])))

;; Natural Natural Doc (-> Doc) -> Doc
(define (better available used doc1 doc2-thunk)
  (if (fits? (- available used) doc1)
      doc1
      (doc2-thunk)))

;; Integer Doc -> Boolean
(define (fits? columns x)
  (and (not (negative? columns)) ;; zero or positive => it might fit
       (match x
         [(cons (? string? s) x1) (fits? (- columns (string-length s)) (force x1))]
         [_ #t]))) ;; the other alternatives are '() and (cons (? integer? i) x1), which always fit

;; Natural DOC [OutputPort] -> Void
(define (pretty-print #:used [used 0] available x [port (current-output-port)])
  (layout port (best available used x)))

;; Natural DOC -> String
(define (pretty-print->string #:used [used 0] available x)
  (call-with-output-string
   (lambda (p) (pretty-print #:used used available x p))))

;;---------------------------------------------------------------------------
;; Utilities

;; DOC ... -> DOC DOC -> DOC
(define (<?> . seps)
  (match seps
    ['() <>]
    [(list sep) (lambda (x y) (<> x (<> sep y)))]
    (seps (lambda (x y) (<> x (<> (<>** seps) y))))))

;; DOC DOC -> DOC
(define <+> (<?> " "))
(define </> (<?> 'line))

;; (DOC DOC -> DOC) (Listof DOC) -> DOC
(define (folddoc f xs)
  (match xs
    ['() ""]
    [(cons x '()) x]
    [(cons x xs1) (f x (folddoc f xs1))]))

;; (Listof DOC) -> DOC
(define (spread xs) (folddoc <+> xs))
(define (stack xs) (folddoc </> xs))
(define (<>* . xs) (folddoc <> xs))
(define (<>** xs) (folddoc <> xs))

;; {#:indent Natural} DOC DOC DOC -> DOC
;; "C"-style bracketing, with delimiters on lines of their own
(define (cbracket #:indent [indent 2] l x r)
  (group (<>* l
              (nest indent (<> 'line x))
              'line r)))

;; DOC DOC -> DOC
(define (<+/> x y) (<> x (<> (-alt " " (lambda () 'line)) y)))

;; String -> DOC
(define (fillwords s) (folddoc <+/> (string-split s)))

;; (Listof DOC) -> DOC
(define (fill #:separator [separator ""] xs)
  (let walk ((xs xs))
    (match xs
      ['() ""]
      [(cons x '()) x]
      [(cons x (cons y zs)) (-alt (<+> (<> (flatten x) separator)
                                       (walk (cons (flatten y) zs)))
                                  (lambda ()
                                    (</> (<> x separator)
                                         (walk (cons y zs)))))])))

;; DOC -> (Listof DOC) -> DOC
(define ((fill* separator) xs) (fill #:separator separator xs))

;;---------------------------------------------------------------------------
;; More utilities

;; String (Listof DOC) DOC -> DOC
;; "Scheme"-style bracketing
(define (sbracket #:separator [separator ""] #:join [join (fill* separator)] l xs r)
  (<>* l
       (nest (string-length l) (join xs))
       r))

(module+ test
  (struct node (label kids) #:prefab)

  (define (node->DOC-0 n)
    (let walk ((n n))
      (match-define (node label kids) n)
      (group (<> label (nest (string-length label)
                             (if (pair? kids)
                                 (<>* "["
                                      (nest 1 (folddoc (<?> "," 'line) (map walk kids)))
                                      "]")
                                 ""))))))

  (define (node->DOC-1 n)
    (let walk ((n n))
      (match-define (node label kids) n)
      (group (<> label (if (pair? kids)
                           (cbracket "["
                                     (folddoc (<?> "," 'line) (map walk kids))
                                     "]")
                           "")))))

  (define (node->DOC-2 n)
    (let walk ((n n))
      (match-define (node label kids) n)
      (group (<> label (nest (string-length label)
                             (if (pair? kids)
                                 (sbracket "[" #:separator "," (map walk kids) "]")
                                 ""))))))

  (define tree1
    (node "aaa" (list (node "bbbbb" (list (node "ccc" '())
                                          (node "dd" '())))
                      (node "eee" '())
                      (node "ffff" (list (node "gg" '())
                                         (node "hhh" '())
                                         (node "ii" '()))))))

  (define narrow (list 14 18 24 80))
  (define wider (list 60 80 100))

  (define (demo-pretty-print widths f v)
    (displayln f)
    (for [(w widths)]
      (displayln (make-string w #\=))
      (pretty-print w (f v))
      (newline))
    (newline))

  (for [(f (list node->DOC-0 node->DOC-1 node->DOC-2))]
    (demo-pretty-print narrow f tree1))

  (define (sexp->DOC-0 s)
    (let walk ((s s))
      (match s
        [(? list? s) (sbracket "(" (map walk s) ")")]
        [(? symbol? s) (symbol->string s)]
        [v (format "~v" v)])))

  (define (sexp->DOC-1 s)
    (let walk ((s s))
      (match s
        [(? list? s) (<>* "(" (nest 1 (group (stack (map walk s)))) ")")]
        [(? symbol? s) (symbol->string s)]
        [v (format "~v" v)])))

  (define sexp->DOC sexp->DOC-1) ;; least-worst option, for use in code->DOC

  (define xexpr
    `(p ((color "red")
         (font "Times")
         (size "10"))
        "Here is some " (em "emphasized") " text."
        "Here is a " (a ((href "http://example.com/")) "link") " elsewhere."))

  (for [(f (list sexp->DOC-0 sexp->DOC-1))]
    (demo-pretty-print narrow f xexpr))

  (define (binder->DOC b)
    (match b
      [(list n e)
       (define head (format "(~a " n))
       (<>* head (nest (string-length head) (code->DOC e)) ")")]
      [other (code->DOC other)]))

  (define (special-seq->DOC #:indent [indent 2] head special->DOC specials normal->DOC normals tail)
    (group (<>* head
                (nest (string-length head) (stack (map special->DOC specials)))
                (if (null? normals)
                    ""
                    (nest indent (<> 'line (stack (map normal->DOC normals)))))
                tail)))

  (define (special-seq->DOC/vertical #:indent [indent 2] head special->DOC specials normal->DOC normals tail)
    (<>* (group (<>* head
                     (nest (string-length head) (stack (map special->DOC specials)))))
         (if (null? normals)
             ""
             (nest indent (<> 'line (stack (map normal->DOC normals)))))
         tail))

  (define (code-seq->DOC left x->DOC xs right)
    (special-seq->DOC left x->DOC xs 'dummy '() right))

  (define (code->DOC c)
    (match c
      [`(define ,h ,bs ...)
       (special-seq->DOC "(define " code->DOC (list h) code->DOC bs ")")]
      [`(lambda ,args ,bs ...)
       (special-seq->DOC "(lambda "
                         values (list (code-seq->DOC "(" code->DOC args ")"))
                         code->DOC bs
                         ")")]
      [`(let ,(? symbol? n) ,args ,bs ...)
       (special-seq->DOC (format "(let ~a " n)
                         values (list (code-seq->DOC "[" binder->DOC args "]"))
                         code->DOC bs
                         ")")]
      [`(quote ,s) (<> "'" (nest 1 (sexp->DOC s)))]
      [(list 'quasiquote s) (<> "`" (nest 1 (code->DOC s)))]
      [(list 'unquote s) (<> "," (nest 1 (code->DOC s)))]
      [(list 'unquote-splicing s) (<> ",@" (nest 2 (code->DOC s)))]
      [`(match ,d ,clauses ...)
       (special-seq->DOC "(match "
                         code->DOC (list d)
                         (match-lambda
                           [`[,p ,bs ...]
                            (code-seq->DOC "[" code->DOC (cons p bs) "]")]
                           [cl
                            ;; if match appears in a pattern (!) there
                            ;; can be weird stuff like ellipsis (...)
                            ;; here
                            (code->DOC cl)])
                         clauses
                         ")")]
      [`(when ,e ,bs ...)
       (special-seq->DOC/vertical "(when "
                                  code->DOC (list e)
                                  code->DOC bs
                                  ")")]
      [`(,(? symbol? n) ,args ...)
       (code-seq->DOC (format "(~a " n) code->DOC args ")")]
      [(? list? s)
       (code-seq->DOC "(" code->DOC s ")")]
      [s (sexp->DOC s)]))

  (demo-pretty-print
   narrow
   code->DOC
   '(define x (+ 1 (* 2 3))))

  (demo-pretty-print
   wider
   code->DOC
   '(define (best available used x)
      (let be ((w available) (k used) (chunks (list (cons 0 x))))
        (when (some-test? chunks)
          (log-info "Here:")
          (log-info "we")
          (log-info "are"))
        (match chunks
          ['()                              '()]
          [(cons (cons i (<> l r)) cs)      (be w k (list* (cons i l) (cons i r) cs))]
          [(cons (cons i (nest j d)) cs)    (be w k (cons (cons (+ i j) d) cs))]
          [(cons (cons i (? string? s)) cs) (cons s (lambda () (be w (+ k (string-length s)) cs)))]
          [(cons (cons i 'line) cs)         (cons i (lambda () (be w i cs)))]
          [(cons (cons i (-alt a b)) cs)    (better w
                                                    k
                                                    (be w k (cons (cons i a) cs))
                                                    (lambda ()
                                                      (be w k (cons (cons i (b)) cs))))]))))

  (demo-pretty-print
   wider
   code->DOC
   '(define (code->DOC c)
      (match c
        [`(define ,h ,bs ...)
         (special-seq->DOC "(define " code->DOC (list h) code->DOC bs ")")]
        [`(lambda ,args ,bs ...)
         (special-seq->DOC "(lambda "
                           values (list (code-seq->DOC "(" code->DOC args ")"))
                           code->DOC bs
                           ")")]
        [`(let ,(? symbol? n) ,args ,bs ...)
         (special-seq->DOC (format "(let ~a " n)
                           values (list (code-seq->DOC "[" binder->DOC args "]"))
                           code->DOC bs
                           ")")]
        [`(quote ,s) (<> "'" (nest 1 (sexp->DOC s)))]
        [(list 'quasiquote s) (<> "`" (nest 1 (code->DOC s)))]
        [(list 'unquote s) (<> "," (nest 1 (code->DOC s)))]
        [(list 'unquote-splicing s) (<> ",@" (nest 2 (code->DOC s)))]
        [`(match ,d ,clauses ...)
         (special-seq->DOC "(match "
                           code->DOC (list d)
                           (match-lambda
                             [`[,p ,bs ...]
                              (code-seq->DOC "[" code->DOC (cons p bs) "]")]
                             [cl
                              ;; if match appears in a pattern (!) there
                              ;; can be weird stuff like ellipsis (...)
                              ;; here
                              (code->DOC cl)])
                           clauses
                           ")")]
        [`(when ,e ,bs ...)
         (special-seq->DOC/vertical "(when "
                                    code->DOC (list e)
                                    code->DOC bs
                                    ")")]
        [`(,(? symbol? n) ,args ...)
         (code-seq->DOC (format "(~a " n) code->DOC args ")")]
        [(? list? s)
         (code-seq->DOC "(" code->DOC s ")")]
        [s (sexp->DOC s)])))

  (define (tag->DOC tag attrs vals kids)
    (define open
      (sbracket (string-append "<" (symbol->string tag) (if (null? attrs) "" " "))
                (map (lambda (a v) (format "~a=~v" a v)) attrs vals)
                (if (null? kids) "/>" ">")))
    (if (null? kids)
        open
        (cbracket open
                  (if (ormap string? kids) ;; mixed content
                      (fill (map xexpr->DOC kids))
                      (stack (map xexpr->DOC kids)))
                  (string-append "</" (symbol->string tag) ">"))))

  (define (xexpr->DOC x)
    (match x
      [(? string? s)
       (fill (string-split s))]
      [(list (? symbol? tag) (list (list (? symbol? attr) (? string? val)) ...) kids ...)
       (tag->DOC tag attr val kids)]
      [(list (? symbol? tag) kids ...)
       (tag->DOC tag '() '() kids)]))

  (demo-pretty-print narrow xexpr->DOC xexpr)

  (demo-pretty-print wider
                     xexpr->DOC
                     '(html
                       (head (meta ((charset "utf-8")))
                             (meta ((http-equiv "X-UA-Compatible") (content "IE=edge")))
                             (meta ((name "viewport") (content "width=device-width, initial-scale=1")))
                             (title "Demo document")
                             (link ((rel "stylesheet") (href "/bootstrap/css/bootstrap.min.css") (type "text/css")))
                             (link ((rel "stylesheet") (href "/jquery-ui.min.css") (type "text/css")))
                             (link ((rel "stylesheet") (href "/style.css") (type "text/css"))))
                       (body (nav ((class "navbar navbar-inverse navbar-fixed-top") (role "navigation"))
                                  (div ((class "container-fluid"))
                                       (div ((class "navbar-header"))
                                            (button ((type "button")
                                                     (class "navbar-toggle collapsed")
                                                     (data-toggle "collapse")
                                                     (data-target "#navbar"))
                                                    (span ((class "sr-only")) "Toggle navigation")
                                                    (span ((class "icon-bar")))
                                                    (span ((class "icon-bar")))
                                                    (span ((class "icon-bar")))))
                                       (div ((id "navbar") (class "collapse navbar-collapse"))
                                            (ul ((class "nav navbar-nav"))))))
                             (div ((class "container"))
                                  (h1 "Heading")
                                  (p "Body"))

                             (script ((type "text/javascript") (src "/jquery.min.js")))
                             (script ((type "text/javascript") (src "/jquery.tablesorter.min.js")))
                             (script ((type "text/javascript") (src "/jquery-ui.min.js")))
                             (script ((type "text/javascript") (src "/bootstrap/js/bootstrap.min.js")))
                             (script ((type "text/javascript") (src "/site.js"))))))
  )

(module+ main
  (require (submod ".." test)))
