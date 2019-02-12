(set-logic UFNIA)
(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) )))

(define-fun base_cases () Bool 
  (and  
    (= (two_to_the 0) 1) 
    (= (two_to_the 1) 2) 
    (= (two_to_the 2) 4) 
    (= (two_to_the 3) 8) 
  )
)


(assert two_to_the_is_ok_full)
(assert (not base_cases))
(check-sat)
