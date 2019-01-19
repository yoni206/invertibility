;(a <op> b) [k:0]
;--->
;a[k:0] <op> b[k:0]


(declare-fun k () Int) ;the k from the commented description
(declare-fun m () Int) ;the width of a and b

(declare-fun a () Int)
(declare-fun b () Int)

(assert (> k 0))
(assert (> m 0))
(assert (< k m))

(assert (in_range m a))
(assert (in_range m b))
(assert two_to_the_is_ok)
(define-fun left () Bool true)
(define-fun right () Bool (= (intextract m k 0 (intmul m a b)) (intmul (+ k 1) (intextract m k 0 a) (intextract m k 0 b))))
