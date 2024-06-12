#lang racket
(require (rename-in "interpreter.rkt" [eval i:eval])
         "error.rkt"
         "conditionals.rkt"
         (except-in trivial reverse length append map curry)
         (prefix-in t: (only-in trivial reverse length append map curry))
         data/collection racket/match point-free)

(define eval (primitive i:eval))

(define (is pred?)
  (foreign
   (procedure-rename
    (λ [in] (if (pred? in) in (raise-error "assertion failure"
                                           "predicate" pred?
                                           "operand" in)))
    (~> (format "is-~s" (object-name pred?)) string->symbol))))

(define var
  (primitive (procedure-rename (λ [v e] (values (ref e v) e)) 'var)))

(define/contract conjify
  (struct/c foreign (-> any/c (struct/c foreign (-> collection? collection?))))
  (local
    [(define (conjify* . v)
       (foreign (λ [coll] (extend coll v))))]
    (foreign (procedure-rename conjify* 'conjify))))

(define (has-count n) (>> (is known-finite?) (is (λ~> count (λ [c] (= c n))))))
(define is-operative? (is operative?))
(define single? (procedure-rename (λ~> rest empty?) 'single?))
(define quote (procedure-rename (λ~> (is single?) first) 'quote))
(define (>> . fs) (composite fs))

(define <:
  (local
    [(struct <: [const] #:transparent
       #:property prop:procedure
       (λ [self op env]
         (match self
           [(<: rand) (combine op rand env)])))]
    (procedure-rename (λ [v] (primitive (<: v))) '<:)))

#;
(define forthify (composite
                  (list eval
                        (or is-operative?
                            (>> var is-operative?)
                            conjify))))