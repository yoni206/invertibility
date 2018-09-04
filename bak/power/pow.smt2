(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)

(define-fun seq ((a Int) (b Int) (k Int) (x Int)) Bool ( = x (mod (+ 1 (* b (+ 1 k))) a)))

;power(a,b,c) <==> a^b=c
;based on https://math.stackexchange.com/questions/312891/how-is-exponentiation-defined-in-peano-arithmetic
(define-fun power ((a Int) (b Int) (c Int)) Bool (exists ((x Int) (y Int)) (and (>= x 0) (>= y 0) (seq x y 0 1) (seq x y b c) (forall ((k Int) (z Int)) (=> (and (>= k 0) (>= z 0) (< k b) (seq x y k z)) (seq x y (+ 1 k) (* a z)))))))
(assert (not (power 2 3 8)))
(check-sat)

