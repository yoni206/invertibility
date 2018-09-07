(set-logic NIA)
(define-fun divtotal ((n Int) (a Int) (b Int)) Int (ite (= b 0) (- n 1) (div a b) ))
(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun in_range ((n Int) (x Int)) Bool (and (>= x 0) (< x n)))
(define-fun range_assumptions ((n Int) (s Int) (t Int)) Bool (and (> n 1) (in_range n s) (in_range n t)))
(define-fun l ((n Int) (x Int) (s Int) (t Int)) Bool <l>)
(define-fun SC ((n Int) (s Int) (t Int)) Bool <SC>)
(define-fun left_to_right ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (SC n s t) (exists ((x Int)) (and (in_range n x) (l n x s t))))))
(define-fun right_to_left ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (exists ((x Int)) (and (in_range n x) (l n x s t))) (SC n s t) )))
(define-fun assertion_ltr_ind () Bool (not (=> (left_to_right k s t) (left_to_right (+ k 1) s t))))
(define-fun assertion_rtl_ind () Bool (not (=> (right_to_left k s t) (right_to_left (+ k 1) s t))))

(assert <assertion>)

(check-sat)


;(declare-fun n () Int)
;(declare-fun s () Int)
;(declare-fun t () Int)
;(assert (not (left_to_right n s t)))
;(check-sat)
;(get-value (n s t))