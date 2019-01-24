;zero_extend(x+t,n) * sign_extend(a,m) < zero_extend(x,n) * sign_extend(a,m)
;--->
;(and
; (not (= t zero))
; (not (= a zero))
; (= (bvult (bvadd x t) x) (bvsgt a zero))
;)


(declare-fun x () Int)
(declare-fun t () Int)
(declare-fun a () Int)


(declare-fun x_w () Int)
(declare-fun t_w () Int)
(declare-fun a_w () Int)

(declare-fun n () Int)
(declare-fun m () Int)

(assert (> x_w 0))
(assert (> t_w 0))
(assert (> a_w 0))

(assert (>= n 0))
(assert (>= m 0))

(assert (= x_w t_w))
(assert (= (+ x_w n) (+ a_w m)))

;n and m are "sufficiently big"
(assert (>= n  x_w))
(assert (>= m  a_w))

(assert (in_range x_w x))
(assert (in_range t_w t))
(assert (in_range a_w a))

(assert two_to_the_is_ok)
(assert (or_is_ok x_w))
(assert (or_is_ok t_w))
(assert (or_is_ok a_w))
(assert (or_is_ok (+ x_w n)))
(assert (or_is_ok (+ a_w m)))

; b - the bv
; b_w - its length
; i - the second argument to sign_extend
(define-fun int_sign_extend ((b_w Int) (b Int) (i Int)) Int (ite (< b (intshl b_w 1 (- b_w 1))) b (intor (+ b_w i) (intshl (+ b_w i) (intnot (+ b_w i) 0) b_w) b )))

(define-fun left () Bool (intslt (+ x_w n) (intmul (+ x_w n) (intadd x_w x t) (int_sign_extend a_w a m)) (intmul (+ x_w n) x (int_sign_extend a_w a m))))
(define-fun right () Bool (and (not (= t 0)) (not (= a 0)) (= (< x_w (intadd x_w x t) x) (intsgt a_w a 0))))
