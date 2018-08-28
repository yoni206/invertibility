(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(define-fun power ((a Int) (b Int) (c Int)) Bool (exists ((F (-> Int Int))) (and (= (F 0) 1) (forall ((i Int))  (=> (and (> i 0) (< i b)) (= (F i) (* (F (- i 1)) a)))) (= (F b)  c) ) ))
(assert (power 2 3 8))
(check-sat)

