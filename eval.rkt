#lang racket

(provide
 (contract-out
  [eval (-> any/c indexable? any)]
  [eval-loop (-> natural? any/c indexable? any)]
  [struct eval-loop/ce [[n natural?]]]
  [eval/ce (and/c eval-loop/ce? operative?)]
  [eval-arg (-> any/c indexable? any)]
  [eval-arg-loop (-> natural? any/c indexable? any)]
  [struct eval-arg-loop/ce [[n natural?]]]
  [eval-arg/ce (and/c eval-arg-loop/ce? operative?)]
  [nest-eval (-> indexable? (-> any/c any/c))]
  [struct applicative [[depth exact-positive-integer?] [op operative?]]]
  [operative? (-> any/c boolean?)]
  [app (-> combiner? applicative?)]
  [appn (and/c (-> exact-positive-integer? combiner? applicative?)
               (-> zero? operative? operative?)
               (-> zero? applicative? applicative?))]
  [unapp (-> applicative? combiner?)])
 (struct-out var)
 gen:argument)

(struct var [name] #:prefab)

(require (except-in "combiner.rkt" if)
         "rrb.rkt" match-plus racket/match
         data/collection racket/generic point-free
         data/pvector)

(define ((env-setter env) val _) (values val env))
(define (drop-env val env) val)

(define (nest-eval env) (λ~> (curryr eval env) drop-env))
(define ((nest-eval-loop n env) val)
  ((~>*) (λ [] (eval-loop n val env)) drop-env))

(define (nest-eval-arg env) (λ~> (curryr eval-arg env) drop-env))
(define ((nest-eval-arg-loop n env [deep? #t]) val)
  ((~>*) (λ [] ((if deep? eval-arg-loop eval-loop) n val env)) drop-env))

(define ((make-evaler init) n val env [deep? #t])
  (values (if (positive? n)
              (extend init (map (nest-eval-arg-loop n env deep?) val))
              val)
          env))

(define (-eval val env)
  (match val
    [(cons (app (nest-eval env) combo) rand)
     (combine combo rand env)]
    [(struct var [name])
     (values (ref env name) env)]))

(define (eval-loop n val env)
  ((~>* val env)
   (cond [(not (and (positive? n) (or (pair? val) (var? val)))) values]
         [(= n 1) -eval]
         [else (λ~> -eval (env-setter env) (curry eval-loop (sub1 n)))])))

(define (eval val env) (eval-loop 1 val env))

(define (eval-arg val env) (eval-arg-loop 1 val env))

(define (eval-seq vals env)
  (define (reduce-eval env init vals)
    (define (tail v) (combine ((nest-eval env) init) v env))
    (match vals
      [(sequence) (eval init env)]
      [(sequence v) (tail v)]
      [(sequence v r ...) (reduce-eval env (tail v) r)]))
  (match vals
    [(? known-finite? (sequence v r ...)) (reduce-eval env v r)]))

(define-generics argument (eval-arg-loop n argument env [deep?])
  #:defaults
  [[hash?
    (define (eval-arg-loop n val env [deep? #t])
      (values
       (if (positive? n)
           (make-immutable-hash
            (hash-map val (λ~> (join identity (nest-eval-arg-loop n env deep?))
                               cons)))
           val)
       env))]
   [rrb? (define eval-arg-loop (make-evaler (rrb)))]
   [(and/c immutable? vector?) (define eval-arg-loop (make-evaler #()))]
   [set? (define eval-arg-loop (make-evaler (set)))]
   [pvector? (define eval-arg-loop (make-evaler (pvector)))]
   [any/c (define (eval-arg-loop n arg env [_ #t]) (eval-loop n arg env))]])

(define (operative? v) (and (combiner? v) (not (applicative? v))))

(define/match* (unapp (applicative (app sub1 n) op)) (appn n op))

(define (app op) (appn 1 op))

(define (appn n op)
  (if (zero? n) op
      (match op
        [(applicative n- op) (appn (+ n n-) op)]
        [op (applicative n op)])))

(struct applicative [depth op] #:transparent #:methods gen:combiner
  [(define/generic cb combine)
   (define/match* (combine (applicative depth op) val env)
     ((~>* val env)
      (curry eval-arg-loop depth)
      (env-setter env)
      (curry cb op)))])

(struct eval-loop/ce [n] #:transparent #:methods gen:combiner
  [(define/match* (combine (eval-loop/ce n) val env) (eval-loop n val env))])

(define eval/ce (eval-loop/ce 1))

(struct eval-arg-loop/ce [n] #:transparent #:methods gen:combiner
  [(define/match* (combine (eval-arg-loop/ce n) val env)
     (eval-arg-loop n val env))])

(struct eval-arg-loop-shallow/ce [n] #:transparent #:methods gen:combiner
  [(define/match* (combine (eval-arg-loop-shallow/ce n) val env)
     (eval-arg-loop n val env #f))])

(define eval-arg/ce (eval-arg-loop/ce 1))