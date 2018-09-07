(set-logic ALL)

(define-fun-rec foo ((k Int) (a Int)) Int
    (ite (<= k 1) 
        0 
        (foo (- k 1) a)))

(define-fun P ((a Int)) Bool (> (foo 1 a) 0))

;(assert (forall ((x Int))  (P x)))
(assert (P 0))

(check-sat)
