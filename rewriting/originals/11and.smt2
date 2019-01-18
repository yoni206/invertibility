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

(assert (in_range k x))
(assert (in_range k y))
(assert (two_to_the_is_ok))

(define-fun left () Bool true)
(define-fun right () Bool (= (intextract k (intand k x y) i j) (intand k (intextract k x i j) (intextract l y i j))))
