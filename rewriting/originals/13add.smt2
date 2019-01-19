;(a <op> b) [i:j]
;--->
;(a[i:0] <op> b[i:0])[i:j]


(declare-fun k () Int) 
(declare-fun i () Int) 
(declare-fun j () Int) 

(declare-fun a () Int)
(declare-fun b () Int)

(assert (> k 0))
(assert (>= i 0))
(assert (>= j 0))
(assert (< i k))
(assert (< j k))
(assert (<= j i))

(assert (in_range k a))
(assert (in_range k b))
(assert two_to_the_is_ok)
(define-fun left () Bool true)
(define-fun right () Bool (= (intextract k i j (intadd k a b)) (intextract k i j (intadd (+ i 1) (intextract k i 0 a) (intextract k i 0 b)))))
