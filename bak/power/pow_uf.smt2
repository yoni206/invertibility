(set-logic UFNIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
 
(declare-fun pow (Int Int) Int) ;(pow(a,b) = a^b)
(define-fun pow_is_ok ((a Int) (b Int)) Bool (and (>= a 0) (>= b 0) (= (pow a 0) 1) (forall ((i Int))  (=> (and (> i 0) (<= i b)) (= (pow a i) (* (pow a (- i 1)) a))))  ) )

(assert (not (= (pow 2 10) 1024)))
(check-sat-assuming ((pow_is_ok 2 10)))

;(assert (not (forall ((x Int)) (> x (F 2 x)))))
;(check-sat (F_IS_OK 2))

