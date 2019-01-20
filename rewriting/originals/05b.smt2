;c^n+m < sign_extend(x^n,m)
;--->
;c[n-1:0] < x   if (c < (1 << (n - 1))) || (c >= ~(1 << (n-1)))
;x[n-1:n-1] = 1 if ~(~0 << (n-1)) <= c <= ~(1 << (n-1))

(declare-fun x () Int)
(declare-fun c () Int)

(declare-fun n () Int)
(declare-fun m () Int)

(assert (> n 0))
(assert (> m 0))

(assert (in_range n x))
(assert (in_range (+ n m) c))

(assert two_to_the_is_ok)

(assert (not (and (<= (intshl (+ n m) (intnot (+ n m) 0) (- n 1)) c) (<= c (intnot (+ n m) (intshl (+ n m) 1 (- n 1)))))))

; b - the bv
; b_w - its length
; i - the second argument to sign_extend
(define-fun int_sign_extend ((b_w Int) (b Int) (i Int)) Int (ite (< b (intshl b_w 1 (- b_w 1))) b (intor (+ b_w i) (intshl (+ b_w i) (intnot (+ b_w i) 0) b_w) b )))

(define-fun left () Bool (< c (int_sign_extend n x m)))
(define-fun right () Bool (= (intextract n (- n 1) (- n 1) x) 1 ))
