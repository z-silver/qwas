#lang racket
(require megaparsack megaparsack/text racket/require
         (multi-in data [collection monad applicative functor]))

(define whitespace/p (or/p eof/p space/p (char/p #\,)))

(define delimiter/p
  (or/p whitespace/p (char-in/p "()[]{}「」『』【】〔〕〈〉《》（）［］｛｝")))

(define (delimited/p open mid close)
  (do open [result <- mid] close (pure result)))

(define (optional/p parser default) (or/p (try/p parser) (pure default)))
(define (mandatory/p parser _) parser)

(define digit-alphabet "0123456789aAbBcCdDeEfF")
(define digit-hash
  (extend (hash) (map (λ [pair] (cons (cdr pair) (car pair)))
                      (indexed (filter (λ [c] (not (char-upper-case? c)))
                                       digit-alphabet)))))

(define (digit*/p base)
  (define base* (- base 10))
  (define taken (+ base (max 0 base*)))
  (do [digit <- (char-in/p (apply string (take taken digit-alphabet)))]
      (pure (hash-ref digit-hash (char-foldcase digit)))))

(define qwas-number-base/p
  (do [base <- (guard/p integer/p (λ [x] (and (>= x 2) (<= x 16)))
                        "decimal integer in [2,16]")]
      (char/p #\b)
      (pure base)))

(define sign*/p
  (do [sign <- (char-in/p "+-")]
      (pure (if (char=? sign #\+) 1 -1))))

(define sign/p (optional/p sign*/p 1))

(define ((make-signed/p sign/p) num/p)
  (do [sign <- sign/p]
      [magnitude <- num/p]
      (pure (* sign magnitude))))

(define opt-signed/p (make-signed/p sign/p))
(define signed/p (make-signed/p sign*/p))

(define (qwas-int/p base)
  (do [digits <- (many+/p (digit*/p base))]
      (pure (foldl (λ [a d] (+ (* a base) d)) 0 digits))))

(define (qwas-rational/p base)
  (define int/p (qwas-int/p base))
  (do [numerator <- int/p]
      [denominator <- (optional/p
                       (do (char/p #\/)
                           (guard/p int/p (and/c integer? (not/c zero?))
                                    "non-zero integer"))
                       1)]
      (pure (/ numerator denominator))))

(define (qwas-complex/p base)
  (define component/p (qwas-rational/p base))
  (define (def v) (if v v 0))
  (do [rational <- (optional/p (opt-signed/p component/p) #f)]
      [imaginary <- ((if rational optional/p mandatory/p)
                     (do [imaginary <- (signed/p (optional/p component/p 1))]
                         (char/p #\i)
                         (pure imaginary))
                     0)]
      (pure (make-rectangular (def rational) imaginary))))

(define qwas-number/p
  (do [base <- (optional/p qwas-number-base/p 10)]
      (qwas-complex/p base)))