(set-logic UFNIA)
(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) )))

(define-fun never_even () Bool
  (forall ((k Int) (x Int)) 
    (=>
      (and (>= k 1) (>= x 0))
      (distinct (- (two_to_the k) 1) (* 2 x))
    )
))

(assert two_to_the_is_ok_full)
(assert (not never_even))
(check-sat)
