(set-logic NIA)
(define-fun divtotal ((n Int) (a Int) (b Int)) Int (ite (= b 0) (- n 1) (div a b) ))
(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun l ((n Int) (x Int) (s Int) (t Int)) Bool (<= (mod (* x s) n) t) )
(define-fun SC ((n Int) (s Int) (t Int)) Bool true
 )
(define-fun in_range ((n Int) (x Int)) Bool (and (>= x 0) (< x n)))

(define-fun range_assumptions ((n Int) (s Int) (t Int)) Bool (and (> n 1) (in_range n s) (in_range n t)))

(define-fun left_to_right ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (SC n s t) (exists ((x Int)) (and (in_range n x) (l n x s t))))))

(define-fun right_to_left ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (exists ((x Int)) (and (in_range n x) (l n x s t))) (SC n s t) )))

(define-fun hypothesis1 () Bool (forall ((n Int) (s Int) (t Int)) (left_to_right n s t)))

(define-fun hypothesis2 () Bool (forall ((n Int) (s Int) (t Int)) (right_to_left n s t)))



;(declare-fun n () Int)

;(declare-fun s () Int)

;(declare-fun t () Int)

;(assert (not (left_to_right n s t)))

;(check-sat)

;(get-value (n s t))

(assert (not hypothesis1))
(check-sat)