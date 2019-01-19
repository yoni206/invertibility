;(x <op> y) [i:j]
;--->
;x[i:j] <op> y[i:j]

(declare-fun k () Int)
(declare-fun i () Int)
(declare-fun j () Int)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (> k 0))
(assert (>= i 0))
(assert (>= j 0))
(assert (< i k))
(assert (< j k))
(assert (<= j i))

(assert (in_range k x))
(assert (in_range k y))
(assert two_to_the_is_ok)
(assert (xor_is_ok k))
(define-fun left () Bool true)
(define-fun right () Bool (= (intextract k (intxor k x y) i j) (intxor (+ (- i j) 1) (intextract k x i j) (intextract k y i j))))
