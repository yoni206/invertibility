;(bvult x (bvadd y 1))
;--->
;(and (not (bvult y x)) (not (= y ~zero)))

(declare-fun k () Int)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (> k 0))
(assert (in_range k x))
(assert (in_range k y))


(define-fun left () Bool (< x (intadd k y 1)))
(define-fun right () Bool (and (not (< y x)) (not (= y (intnot k 0)))))
