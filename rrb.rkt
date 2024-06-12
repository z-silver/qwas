#lang racket
(provide
 (contract-out
  [rename make-rrb rrb (-> any/c ... rrb?)]
  [rrb? (-> any/c boolean?)]
  [in-rrb (-> rrb? seq?)]
  [rrb->stream (-> rrb? stream?)]
  [rrb-pop (-> (and/c rrb? (not/c empty?)) rrb?)]
  [rrb-last (-> (and/c rrb? (not/c empty?)) any/c)]
  [empty-rrb (and/c rrb? empty?)]
  [rrb-map (-> (-> any/c any/c) rrb? rrb?)]
  [rrb-drop (-> exact-nonnegative-integer? rrb? rrb?)]
  [rrb-drop-right (-> exact-nonnegative-integer? rrb? rrb?)]
  [rrb-take (-> exact-nonnegative-integer? rrb? rrb?)]
  [rrb-take-right (-> exact-nonnegative-integer? rrb? rrb?)]))

;; I never did finish this one
;; and as of Racket 8.13, this is entirely redundant

(require (only-in racket/base [sequence? seq?])
         racket/match data/collection
         match-plus racket/generic racket/struct)

;; bit partitioning size
(define/contract shift-interval exact-positive-integer? 5)

(define (add-height shift) (- shift shift-interval))
(define (sub-height shift) (+ shift shift-interval))
(define max-height min)
(define height1 (add-height 0))

;; branching factor
(define/contract max-error natural? 2)

(define max-size (arithmetic-shift 1 shift-interval))
(define mask (sub1 max-size))
(define (max-size? n) (= n max-size))
(define (leaf-full? vec) (= (vector-length vec) max-size))
(define (relax-size? vec) (< (vector-length vec) max-size))
(define (acceptable? vec) (<= (vector-length vec) max-size))

(define (shift->length shift) (arithmetic-shift max-size (abs shift)))
(define (idx->leaf-idx n) (bitwise-and n mask))


(define (size->max-leaves n) (+ max-error (ceiling (/ n max-size))))

(define danger 'danger)
(define (danger? v) (eq? v danger))

;; vector helpers
(define empty-vec #())

(define ->ivec vector->immutable-vector)
(define ivec (compose1 ->ivec vector))

(define (ivec-take vec n) (->ivec (if (= n (vector-length vec)) vec
                                      (vector-take vec n))))
(define (ivec-drop vec n) (->ivec (if (zero? n) vec
                                      (vector-drop vec n))))
(define (ivec-but-last vec) (->ivec (vector-drop-right vec 1)))
(define (ivec-set-last vec val) (set-nth vec (sub1 (length vec)) val))
(define (last? idx vec) (= idx (sub1 (vector-length vec))))

(define leaf?
  (flat-named-contract 'leaf? (and/c vector? immutable? acceptable?)))

(define (in-branch node)
  (apply sequence-append (map in-node (branch-vec node))))

(define (in-node node)  
  (cond [(leaf? node) (in-vector node)]
        [(branch? node) (in-branch node)]))

(define yes (const #t))

;; rrb head
(define/match* (in-rrb (rrb _ _ root tail))
  (sequence-append (in-node root) (in-node tail)))

(define rrb->stream (compose1 sequence->stream in-rrb))

(define/match* (rrb-map f (rrb root-size length root tail))
  (define (leaf-map f v) (vector->immutable-vector (vector-map f v)))
  (define (map* f v)
    (define/match* (branch-map f (branch size shift size-vec vec))
      (branch size shift size-vec (leaf-map (curry map* f) vec)))
    ((if (vector? v) leaf-map branch-map) f v))
  (if (zero? length) empty-rrb
      (rrb root-size length (map* f root) (leaf-map f tail))))

(struct rrb [root-length length root tail] #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer (const 'rrb) in-rrb))]
  #:methods gen:collection
  [(define/generic -conj conj)
   (define/match* (conj (rrb root-length (app add1 length) root tail) elt)
     (cond [(leaf-full? tail)
            (rrb (+ root-length max-size) length (push root tail) (ivec elt))]
           [(relax-size? tail) (rrb root-length length root (-conj tail elt))]))
   (define (extend left right)
     (cond [(empty? right) left]
           [(rrb? right) (rrb-concat left right)]
           [(leaf? right) (tail-concat left right)]
           [else (foldl conj left right)]))]
  #:methods gen:countable
  [(define known-finite? yes)
   (define (length node) (rrb-length node))]
  #:methods gen:sequence
  [(define/match* (nth (rrb root-length length root tail) idx)
     (cond [(< idx root-length) (lookup root idx)]
           [(< idx length) (vector-ref tail (- idx root-length))]))
   (define rest (compose1 stream-rest rrb->stream))
   (define/match* (update-nth (and vec (rrb root-length length root tail))
                              idx f)
     (cond [(< idx root-length)
            (let [[new-root (update root idx f)]]
              (if (equal? root new-root) vec
                  (rrb root-length length new-root tail)))]
           [(< idx length)
            (let [[new-tail (update tail (- idx root-length) f)]]
              (if (equal? tail new-tail) vec
                  (rrb root-length length root new-tail)))]))
   (define (set-nth vec idx val) (update-nth vec idx (const val)))
   (define random-access? yes)])

(define empty-rrb (rrb 0 0 empty-vec empty-vec))

(define (equal-length? l r) (= (length l) (length r)))

(define (rrb-equal? l r recur)
  (and (equal-length? l r) (sequence-andmap recur (in-parallel l r))))

(define (lookup node idx)
  (match node
    [(? leaf?) (vector-ref node (idx->leaf-idx idx))]
    [(branch _ shift size-vec vec)
     (define-values [vec-idx nest-idx] (search idx shift size-vec))
     (lookup (vector-ref vec vec-idx) nest-idx)]))

(define (update node idx f)
  (match node
    [(? leaf?)
     (let [[idx (idx->leaf-idx idx)]]
       (define old (nth node idx))
       (define new (f old))
       (if (equal? old new) node (set-nth node idx new)))]
    [(branch length shift size-vec vec)
     (define-values [vec-idx nest-idx] (search idx shift size-vec))
     (define old (vector-ref vec vec-idx))
     (define new (update old nest-idx f))
     (if (eq? old new) node
         (branch length shift size-vec (set-nth vec vec-idx new)))]))

(struct branch [length shift density vec] #:transparent
  #:methods gen:countable
  [(define known-finite? yes)
   (define (length v) (branch-length v))]
  #:methods gen:sequence
  [(define nth lookup)
   (define rest (compose1 stream-rest sequence->stream in-branch))
   (define random-access? yes)
   (define update-nth update)
   (define (set-nth node idx val) (update node idx (const val)))])

(define (leaf-next-level . leaves)
  (branch* height1 (extend empty-vec leaves)))

(define (end-slice node vec)
  (if (empty? node) (ivec-but-last vec) (ivec-set-last vec node)))

(define (pop node)
  (define (vec-values vec)
    (values (vector-ref vec 0) (vector-ref vec 1)))
  (define (sub-max-size n) (- n max-size))
  (define (pop-vector vec)
    (define-values [node tail] (pop (last vec)))
    (values (end-slice node vec) tail))
  (match node
    [(? leaf?) (values empty-vec node)]
    [(branch _ _ _ (vector left (? leaf? right)))
     (try-consolidate left right)]
    [(branch length shift density old-vec)
     (define-values [vec tail] (pop-vector old-vec))
     (try-consolidate
      (match vec
        [(vector) empty-vec]
        [(vector node) node]
        [(? leaf?)
         (if (vector? density) (branch** vec)
             (branch (- length (if density (vector-length tail) max-size))
                     shift #f vec))])
      tail)]))

(define (search idx shift density [idx-preserving? #t])
  (define guess (bitwise-and (arithmetic-shift idx shift) mask))
  (if (not (vector? density))
      (values guess
              (if idx-preserving? idx
                  (bitwise-and idx
                               (sub1 (shift->length (sub-height shift))))))
      (let [[size-vec-ref (curry vector-ref density)]]
        (let loop [[guess guess]
                   [lo (if (zero? guess) 0 (size-vec-ref (sub1 guess)))]
                   [hi (size-vec-ref guess)]]
          (if (< idx hi) (values guess (- idx lo))
              (let [[next (add1 guess)]]
                (loop next hi (size-vec-ref next))))))))

(define/match* (unsafe-rrb-take n (and vec (rrb root-size rrb-size root tail)))
  (define (node-take n node)
    (define node-size (length node))
    (cond [(= n node-size) (pop node)]
          [(< n node-size)
           (match node
             [(? leaf?) (values empty-vec (ivec-take node n))]
             [(branch _ shift size-vec vec)
              (define last-idx (sub1 n))
              (define-values [vec-idx nest-idx]
                (search last-idx shift size-vec #f))
              (define nest-size (add1 nest-idx))
              (if (zero? vec-idx)
                  (let [[node (vector-ref vec vec-idx)]]
                    (node-take nest-size node))
                  (let* [[vec-size (add1 vec-idx)]
                         [vec (ivec-take vec vec-size)]]
                    (define-values [node tail]
                      (node-take nest-size (vector-ref vec vec-idx)))
                    (values (branch** (end-slice node vec)) tail)))])]))
  (cond [(zero? n) empty-rrb]
        [(<= n root-size)
         (let*-values [[[root tail] (node-take n root)]
                       [[root tail] (try-consolidate root tail)]]
           (rrb (length root) n root tail))]
        [(< n rrb-size)
         (rrb root-size n root (ivec-take tail (- n root-size)))]
        [(= n rrb-size) vec]))

(define/match* (unsafe-rrb-drop n (and vec
                                       (rrb root-length rrb-length root tail)))
  (define (node-drop n node)
    (match node
      [(? leaf?) (ivec-drop node n)]
      [(branch _ shift length-vec vec)
       (define-values [vec-idx nest-idx] (search n shift length-vec #f))
       (if (last? vec-idx vec)
           (node-drop nest-idx (last vec))
           (branch** (update-nth (ivec-drop vec vec-idx) 0
                                 (curry node-drop nest-idx))))]))
  (cond [(zero? n) vec]
        [(= n rrb-length) empty-rrb]
        [else
         (let [[final-size (- rrb-length n)]]
           (cond [(< n root-length)
                  (let [[root (node-drop n root)]]
                    (let-values [[[root tail] (try-consolidate root tail)]]
                      (rrb (length root) final-size root tail)))]
                 [(< n rrb-length)
                  (rrb 0 final-size empty-vec
                       (ivec-drop tail (- n root-length)))]))]))

(define (rrb-range-check sym n vec)
  (when (< (length vec) n)
    (raise-range-error sym "rrb" "" n vec 0 (length vec))))

(define (rrb-take n vec)
  (rrb-range-check 'rrb-take n vec)
  (unsafe-rrb-take n vec))

(define (rrb-drop n vec)
  (rrb-range-check 'rrb-drop n vec)
  (unsafe-rrb-drop n vec))

(define (rrb-drop-right n vec)
  (rrb-range-check 'rrb-drop-right n vec)
  (unsafe-rrb-take (- (length vec) n) vec))

(define (rrb-take-right n vec)
  (rrb-range-check 'rrb-take-right n vec)
  (unsafe-rrb-drop (- (length vec) n) vec))

(define node-length length)

(define (branch* shift vec)
  (define (full-leaf? node)
    (and (leaf? node) (leaf-full? node)))
  (define (fully-dense-node? node)
    (or (full-leaf? node)
        (and (branch? node)
             (not (branch-density node)))))
  (define (dense-node? node)
    (or (leaf? node)
        (and (branch? node)
             (not (vector? (branch-density node))))))
  (define (full-node? shift node)
    (= (length node) (shift->length shift)))
  (define (node-vec->length+density shift vec)
    (define (but-last vec) (take (sub1 (vector-length vec)) vec))
    (define (add-size n node) (+ n (node-length node)))
    (define (return-size-vec)
      (let [[size-vec (extend empty-vec (rest (foldl/steps add-size 0 vec)))]]
        (values (last size-vec) size-vec)))
    (if (sequence-andmap (curry full-node? shift) (but-last vec))
        (let* [[tail (last vec)]
               [new-density (cond [(fully-dense-node? tail) #f]
                                  [(dense-node? tail) danger]
                                  [else empty-vec])]]
          (if (vector? new-density)
              (return-size-vec)
              (values (foldl add-size 0 vec) new-density)))
        (return-size-vec)))
  (cond [(zero? shift) vec]
        [(leaf? vec)
         (let-values [[[size size-vec]
                       (node-vec->length+density (sub-height shift) vec)]]
           (branch size shift size-vec vec))]))

(define (branch** vec)
  (define (step shift node)
    (define (node-shift node)
      (cond [(leaf? node) 0]
            [(branch? node) (branch-shift node)]))
    (max-height shift (node-shift node)))
  (if (empty? vec) empty-vec
      (branch* (add-height (foldl step 0 vec)) vec)))

(define (push node leaf) ; (-> node? leaf? node?)
  (define (make-branch length)
    (define (dense-node* shift vec)
      (branch (+ max-size length) shift #f vec))
    (cond [(leaf-full? leaf) dense-node*]
          [(relax-size? leaf) branch*]))
  (if (empty? leaf) node
      (match node
        [(? empty?) leaf]
        [(? leaf?) (leaf-next-level node leaf)]
        [(branch length shift #f _)
         #:when (= length (shift->length shift))
         ((make-branch length) (add-height shift) (ivec node leaf))]
        [(branch size shift #f vec)
         ((make-branch size)
          shift
          (if (zero? ; (modulo size (shift->length (sub-height shift)))
               (bitwise-and size (sub1 (shift->length (sub-height shift)))))
              (conj vec leaf)
              (update-nth vec (sub1 (vector-length vec))
                          (curryr push leaf))))])))

(define make-rrb (local [(define (rrb . vals) (extend empty-rrb vals))] rrb))

(define/match* (rrb-last (rrb _ _ _ tail))
  (vector-ref tail (sub1 (vector-length tail))))

(define/match* (rrb-pop (rrb _ (app sub1 length) root tail))
  (cond
    [(negative? length) (error "attempt to pop empty rrb shouldn't happen")]
    [(zero? length) empty-rrb]
    [else (let-values [[[root tail]
                        (match tail
                          [(vector _) (pop root)]
                          [(vector) (error "empty rrb tail shouldn't happen")]
                          [_ (values root (ivec-but-last tail))])]]
            (rrb (length root) length root tail))]))

(define (try-consolidate left right)
  (define (branch-consolidate left right)
    (define-values [left* middle] (pop left))
    (define-values [new-middle new-right] (tail-consolidate middle right))
    (values (push left* new-middle) new-right))
  (define consolidate
    (cond [(leaf? left) tail-consolidate]
          [(danger? (branch-density left)) branch-consolidate]
          [else values]))
  (consolidate left right))

(define (tail-consolidate left right)
  ; (-> leaf? leaf? (values leaf? leaf?))
  (define left-length (vector-length left))
  (define right-length (vector-length right))
  (cond [(zero? right-length) (values empty-vec left)]
        [(max-size? left-length) (values left right)]
        [(zero? left-length) (values empty-vec right)]
        [else
         (let [[elements (+ left-length right-length)]]
           (if (<= elements max-size) (values empty-vec (extend left right))
               (let [[left-builder
                      (λ [idx] (if (< idx left-length) (vector-ref left idx)
                                   (vector-ref right (- idx left-length))))]
                     [right-builder
                      (λ [idx]
                        (define start (- max-size left-length))
                        (vector-ref right (+ start idx)))]]
                 (values (->ivec (build-vector max-size left-builder))
                         (->ivec (build-vector (- elements max-size)
                                               right-builder))))))]))

(define (merge left right [recur? #f])
  (cond
    [(and left right)
     (cond
       [(leaf? left)
        (if (leaf? right) (tail-consolidate left right)
            (merge (leaf-next-level left) right recur?))])]
    [left => pop]
    [right => pop]))

(define (special-vector-foldl f acc end vec)
  (define size (length vec))
  (define (end? n) (= n size))
  (let loop [[acc acc]
             [res empty-vec]
             [pos 0]]
    (if (end? pos)
        (let-values [[[new-res acc] (f acc end)]]
          (values (conj res new-res) acc))
        (let-values [[[new-res acc] (f acc (nth pos vec))]]
          (loop acc (conj res new-res) (add1 pos))))))

(define (special-vector-foldl1 f end vec)
  (define acc (first vec))
  (define tail (rest vec))
  (special-vector-foldl f acc end tail))

(define (rrb-with-sizes left right root tail)
    (rrb (length root) (+ left right) root tail))

(define/match* (tail-concat (rrb _ length old-root old-tail) tail)
  (define tail-length (vector-length tail))
  (let-values [[[pushed tail] (tail-consolidate old-tail tail)]]
    (define root (push old-root pushed))
    (rrb-with-sizes length tail-length root tail)))

(define (rrb-concat left right)
  (match* [left right]
    [[(? empty?) right] right]
    [[left (? empty?)] left]
    [[left (rrb _ _ (? empty?) right-tail)]
     (tail-concat left right-tail)]
    [[(rrb _ left-size left-root left-tail)
      (rrb _ right-size right-root right-tail)]
     (let [[root (merge (push left-root left-tail) right-root)]]
       (rrb-with-sizes left-size right-size root right-tail))]))
