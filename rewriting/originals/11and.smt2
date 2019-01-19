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
(assert (and_is_ok k))
(define-fun left () Bool true)
(define-fun right () Bool (= (intextract k i j (intand k x y)) (intand (+ (- i j) 1) (intextract k i j x) (intextract k i  j y))))
