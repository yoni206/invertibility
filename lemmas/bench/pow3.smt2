(set-logic UFNIA)
(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) )))

(define-fun strong_monotinicity () Bool
    (forall ((i Int) (j Int)) 
      (=> 
	(and (>= i 0) (>= j 0) ) 
	(=> (< i j) (< (two_to_the i) (two_to_the j)))
      )
    )
)

(assert two_to_the_is_ok_full)
(assert (not strong_monotinicity))
(check-sat)
