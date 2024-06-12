#lang racket
;; Note on Contracts
;;
;; Although the contracts below have a return value of any, the actual
;; requirement is a return value of (values any/c indexable?).
;; In order to preserve proper tail calls, we do not enforce that requirement.
;; Doing so is safe because the procedures will be composed serially anyways,
;; and the next procedure is already checking that same invariant on its input.

;; See John Shutt's work on the vau cauculus for useful background.

(provide 
 (contract-out
  [struct composite [[op (and/c known-finite?
                                (sequenceof combiner? #:chaperone? #t))]]]
  [composite* (-> (and/c known-finite? (sequenceof combiner? #:chaperone? #t))
                  combiner?)]
  [struct foreig1 [[op (-> any/c any/c)]]]
  [struct foreign [[op (-> any/c ... any/c)]]]
  [struct if [[try combiner?] [then combiner?] [else combiner?]]]
  [rename $if if* (-> combiner? combiner? combiner? combiner?)]
  [struct fail [[sym symbol?] [msg string?]]]
  [rename $id id (and/c combiner? id?)]
  [struct fix [[op (-> fix? combiner?)]]]
  [struct fix* [[ops (hash/c any/c (-> fix* combiner?) #:immutable #t)]]]
  [struct ext [[seq sequence?]]]
  [struct bind [[names hash?]]]
  [struct unbind [[names set?]]]
  [struct initve [[val any/c] [env indexable?]]]
  [struct initv [[val any/c]]]
  [struct inite [[env indexable?]]]
  [struct op->proc [[op combiner?] [env indexable?]]])
 gen:combiner combine combiner? id?)

(module interface racket
  (provide gen:combiner (rename-out [comb? combiner?])
           (contract-out [combine (-> comb? any/c indexable? any)]))
  
  (require racket/generic data/collection)

  (struct var [name] #:prefab)
  
  (define-generics combiner (combine combiner val env)
    #:defined-predicate combiner-implements?
    #:fast-defaults
    [[symbol? (define (combine sym coll env) (values (ref coll sym) env))]
     [var? (define (combine v coll env) (values (ref coll (var-name v)) env))]
     [set? (define (combine set val env)
             (if (set-member? set val)
                 (values val env)
                 (raise-arguments-error 'combine "value not found in set"
                                        "set" set
                                        "value" val)))]]
    #:defaults
    [[indexable? (define (combine coll val env) (values (ref coll val) env))]])
  
  (define comb?
    (let [[combo? combiner?]]
      (define (combiner? v)
        (and (combo? v) (combiner-implements? v 'combine)))
      combiner?)))

(require 'interface data/collection racket/match match-plus racket/generic
         point-free (only-in racket [if if*]) "rrb.rkt")

(struct composite [op] #:transparent #:methods gen:combiner
  [(define/generic cb combine)
   (define/match* (combine (composite op) val env)
     (let run [[op op] [val val] [env env]]
       (match op
         [(sequence) (values val env)] ; fail-safe, return if done
         [(sequence op) (cb op val env)] ; ensure proper tail calls
         [(sequence op rest ...) ((~>* op val env) cb (curry run rest))])))])

(define (composite* op)
  (define (take-until pred? seq)
    (match seq
      [(sequence) empty-stream]
      [(sequence (? pred? last) _ ...) (stream-cons last empty-stream)]
      [(sequence non-pred rest ...)
       (stream-cons non-pred (take-until pred? rest))]))
  (match (take-until fail? (filter (not/c id?) op))
    [(sequence) $id]
    [(sequence op) op]
    [_ (composite (extend (rrb) op))]))

(struct foreig1 [op] #:transparent #:methods gen:combiner
  [(define/match* (combine (foreig1 op) val env) (values (op val) env))])

(struct foreign [op] #:transparent #:methods gen:combiner
  [(define/match* (combine (foreign op) val env)
     (values ((~>* op val) apply rrb) env))])

(struct if [try then else] #:transparent #:methods gen:combiner
  ;; See Mark Tullsen's paper First Class Patterns for background.
  ;; Here we implement the Maybe monad in terms of exception throwing
  ;; i.e. a normal return is a Just result, and an exception is a Nothing.
  ;; See also Lua's pcall function.
  [(define/generic cb combine)
   (define/match* (combine (if try then else) val env)
     ((~>*)
      (λ [] (with-handlers ([exn:fail? (λ [_] (values #f val env))])
              ((~>* try val env) cb (λ [val env] (values #t val env)))))
      (λ [success? val env] (cb (if* success? then else) val env))))])

(define ($if try then else)
  (cond [(id? try) then]
        [(fail? try) else]
        [else (if try then else)]))

(struct fix [op] #:transparent #:methods gen:combiner
  ;; This is basically the Y combinator in struct form.
  [(define/generic cb combine)
   (define/match* (combine (and self (fix op)) val env)
     (cb (op self) val env))])

(struct fix* [ops] #:transparent #:methods gen:combiner
  ;; And this is the polyvariadic version, using a hash.
  [(define/match* (combine (and self (fix* ops)) val env)
     (values ((ref ops val) self) env))])

(struct id [] #:transparent #:methods gen:combiner
  [(define (combine _ val env) (values val env))])

(define $id (id))

(struct fail [sym msg] #:transparent #:methods gen:combiner
  [(define/match* (combine (fail sym msg) val env)
     (raise-arguments-error sym msg "operand" val "environment" env))])

(struct ext [seq] #:transparent #:methods gen:combiner
  [(define/match* (combine (ext seq) val env) (values (extend val seq) env))])

(struct bind [names] #:transparent #:methods gen:combiner
  [(define/match* (bind-pair env (cons key val)) (set-ref env key val))
   (define/match* (combine (bind names) val env)
     (values val (foldl bind-pair env names)))])

(struct unbind [names] #:transparent #:methods gen:combiner
  [(define/match* (combine (unbind names) val env)
     (values val (foldl dict-remove env names)))])

(struct initve [val env] #:transparent #:methods gen:combiner
  [(define/match* (combine (initve val env) _ _) (values val env))])

(struct initv [val] #:transparent #:methods gen:combiner
  [(define/match* (combine (initv val) _ env) (values val env))])

(struct inite [env] #:transparent #:methods gen:combiner
  [(define/match* (combine (inite env) val _) (values val env))])

(struct bind-env [name] #:transparent #:methods gen:combiner
  [(define empty-hash (hash))
   (define/match* (combine (bind-env name) val env)
     (values val (set-ref empty-hash name env)))])

(struct explode-env [name] #:transparent #:methods gen:combiner
  [(define/match* (combine (explode-env name) val env)
     (values val (ref env name)))])

(struct op->proc [op env] #:transparent #:property prop:procedure
  (match-lambda** [[(op->proc op env) val] (combine op val env)]))