(set-logic UFNIA)
(define-fun-rec pow ((a Int)(b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(declare-fun x () Int)

(assert (>= (mod (div x (pow 2 s)) (pow 2 k)) t))
(assert (not (= (mod (* t (pow 2 s)) (pow 2 k)) t)))

(assert (>= s 2))
(assert (>= t 2))
(assert (>= x 3))

(check-sat)
(get-value (k s t x (pow 2 3)))

