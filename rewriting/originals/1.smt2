;sign_extend(x+t,n) * sign_extend(a,m) < sign_extend(x,n) * sign_extend(a,m)
;--->
;(and                                                                                                                                                           
; (not (= t zero))                                                                   
; (not (= a zero))                                                                   
; (= (bvslt (bvadd x t) x) (bvsgt a zero))                                           
;)

;TODO how to do sign_extend?
;TODO this file actually does zero_extend...

(declare-fun x_w () Int)
(declare-fun t_w () Int)
(declare-fun a_w () Int)
(declare-fun m () Int)
(declare-fun n () Int)

(declare-fun x () Int)
(declare-fun t () Int)
(declare-fun a () Int)

(assert (> n 0))
(assert (> m 0))
(assert (> x_w 0))
(assert (> t_w 0))
(assert (> a_w 0))

(assert (= x_w t_w))
(assert (= (+ x_w n) (+ a_w m)))
(assert (= (+ x_w n) (+ a_w m)))

(define-fun left () Bool (< (intmul (+ x_w n) (intadd (+ x_w n) x t ) a) (intmul (+ x_w n) x a ) ))
(define-fun right () Bool (and (not (= t 0)) (not (= a 0)) (= (intslt x_w (intadd x_w x t) x) (intsgt a_w a 0))))

