(set-logic UFNIA)
(define-fun-rec pow ((a Int)(b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))
(declare-fun x () Int)
(assert (and (>= x 0) (>= x (pow 2 x))))
(check-sat)
(get-value (x (pow 2 0) (pow 2 1) (pow 2 2) (pow 2 3)))

