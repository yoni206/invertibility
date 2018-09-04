(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(define-fun power ((a Int) (b Int) (c Int)) Bool (exists ((A (Array Int Int))) (and (= (select A 0) 1) (forall ((i Int))  (=> (and (> i 0) (< i b)) (= (select A i) (* (select A (- i 1)) a)))) (= (select A b)  c) ) ))
(assert (not (power 2 3 8)))
(check-sat)

