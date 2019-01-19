;sign_extend(x^n, m) = c^n+m
;--->
;x = c[n-1:0]   if (c[n-1:n-1] == 0 && c[n+m-1:n] == 0) || (c[n-1:n-1] == 1 && c[n+m-1:n] == ~0)
;false          otherwise

(declare-fun x () Int)
(declare-fun c () Int)

(declare-fun n () Int)
(declare-fun m () Int)

(assert (> n 0))
(assert (> m 0))

(assert (in_range x n))
(assert (in_range c (+ n m)))

(assert two_to_the_is_ok)



; b - the bv
; b_w - its length
; i - the second argument to sign_extend
(define-fun int_sign_extend ((b_w Int) (b Int) (i Int)) Int (ite (< b (intshl b_w 1 (- b_w 1))) b (intor (+ b_w i) (intshl (+ b_w i) (intnot (+ b_w i) 0) b_w) b )))

(define-fun left () Bool (= (int_sign_extend n x m) c))
(define-fun right () Bool (ite (or (and (= (intextract (+ n m) (- n 1) (- n 1) c) 0) (= (intextract (+ n m) (- (+ n m) 1) n c) 0) ) (and (= (intextract (+ n m) (- n 1) (- n 1) c) 1) (= (intextract (+ n m) (- (+ n m) 1) n c) (intnot m 0)) )) (= x (intextract (+ n m) (- n 1) 0 c)) false))
