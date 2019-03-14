(set-logic UFNIA)
(declare-fun two_to_the (Int) Int) 

;complete axiomatization
(define-fun full_def () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (!(=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) :pattern ((instantiate_me i))) )))

;some fixed values
(define-fun base_cases () Bool 
  (and  
    (= (two_to_the 0) 1) 
    (= (two_to_the 1) 2) 
    (= (two_to_the 2) 4) 
    (= (two_to_the 3) 8) 
  )
)

;weak-monotinicity
(define-fun weak_monotinicity () Bool
    (forall ((i Int) (j Int)) 
      (=> 
	(and (>= i 0) (>= j 0) ) 
 	(=> (<= i j) (<= (two_to_the i) (two_to_the j))) 
      )
    )
)

;strong-monotinicity
(define-fun strong_monotinicity () Bool
    (forall ((i Int) (j Int)) 
      (=> 
	(and (>= i 0) (>= j 0) ) 
	(=> (< i j) (< (two_to_the i) (two_to_the j)))
      )
    )
)

;if 2^i mod 2^j is not 0, then i<j
(define-fun modular_power () Bool
  (forall ((i Int) (j Int) (x Int))
    (!
      (=> 
        (and (>= i 0) (>= j 0) (>= x 0) (distinct (mod (* x (two_to_the i)) (two_to_the j)) 0))
        (< i j)
      )
     :pattern ((instantiate_me i) (instantiate_me j) (instantiate_me x)))
  )
)

;2^k -1 is never even, provided that k != 0
(define-fun never_even () Bool
  (forall ((k Int) (x Int)) 
   (!
    (=>
      (and (>= k 1) (>= x 0))
      (distinct (- (two_to_the k) 1) (* 2 x))
    )
    :pattern ((instantiate_me k) (instantiate_me x)))
  )
)

;2^k>=1
(define-fun always_positive () Bool
  (forall ((k Int)) 
   (!
    (=>
      (>= k 0)
      (>= (two_to_the k) 1) 
    )
    :pattern ((instantiate_me k)))
  )
)

;x div 2^x is zero
(define-fun div_zero () Bool
  (forall ((k Int)) 
   (!
    (=>
      (>= k 0)
      (= (div k (two_to_the k)) 0 ) 
    )
    :pattern ((instantiate_me k)))
  )
)

(define-fun two_to_the_is_ok () Bool 
  (and
     full_def
     base_cases
     weak_monotinicity
     strong_monotinicity
     modular_power
     never_even    
     always_positive
     div_zero
  )
)

(assert two_to_the_is_ok)
