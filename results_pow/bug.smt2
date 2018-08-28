(set-logic UFNIA)
(define-fun-rec pow ((a Int)(b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))
(assert true)
(check-sat)
(get-value ((pow 2 3)))
