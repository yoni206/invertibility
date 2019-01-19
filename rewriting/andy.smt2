(set-logic UFNIA)

(declare-fun two_to_the (Int) Int)
(declare-fun instantiate_me (Int) Bool)

;complete axiomatization of power
(define-fun two_to_the_is_ok () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (!(and (instantiate_me i) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2)))) :pattern ((instantiate_me i))) )))

(assert two_to_the_is_ok)
(assert (= 1 1))
(check-sat)

(get-value ((two_to_the 0)))
