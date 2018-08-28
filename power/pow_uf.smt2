(set-logic UFNIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
 
(declare-fun F (Int Int) Int) ;(F(a,b) = a^b)
(define-fun F_IS_OK ((a Int)) Bool (and (>= a 0) (= (F a 0) 1) (forall ((i Int))  (=> (and (> i 0)) (= (F a i) (* (F a (- i 1)) a))))  ) )

(assert (not (= (F 2 10) 1023)))
(check-sat (F_IS_OK 2))

;(assert (not (forall ((x Int)) (> x (F 2 x)))))
;(check-sat (F_IS_OK 2))

