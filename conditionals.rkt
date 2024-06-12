#lang racket
(provide
 (contract-out
  [struct predicate [[op (and/c (not/c predicate?) combiner?)]]]
  [pred (-> combiner? predicate?)]
  [cond (-> combiner? ...  combiner?)]
  [cond-not (-> combiner? ... combiner?)]
  [or (-> combiner? ... combiner?)]
  [not (-> combiner? combiner?)]))

(require (except-in "combiner.rkt" if) data/collection
         syntax/parse/define racket/generic match-plus)

(define (conditional nullary general)
  (case-lambda
    [[] nullary]
    [[op] op]
    [else (apply general else)]))

(define-simple-macro (define-cond (name:id . args:expr) default:expr body:expr)
  (define name (procedure-rename (conditional default (λ args body)) 'name)))

(define cond-fail (fail 'cond "branch failure, no matching pattern"))
(define or-fail (fail 'or "branch failure, nullary or"))
(define not-fail (fail 'not "branch failure, inverted pattern succeeded"))

(define-cond (cond try then . else) cond-fail (if* try then (apply cond else)))
(define-cond (cond-not try else . then) id (if* try (apply cond-not then) else))

(define-cond (or op . ops) or-fail (if* op id (apply or ops)))

(define (not op) (if* op not-fail id))

(struct predicate [op] #:transparent #:methods gen:combiner
  [(define/generic cb combine)
   (define/match* (combine (predicate op) val env)
     (cb op val env)
     (values val env))])

(define (pred op) (if (predicate? op) op (predicate op)))