;sign_extend(x^n,m) < c^n+m to
;--->
;x < c[n-1:0]   if (c <= (1 << (n - 1))) || (c >= (~0 << (n - 1)))
;x[n-1:n-1] = 0 if (1 << (n - 1)) < c <= (~0 << (n - 1))

;precondition: 
;~(~0 << (n - 1)) == (1 << (n - 1)) - 1


(declare-fun x () Int)
(declare-fun c () Int)

(declare-fun n () Int)
(declare-fun m () Int)

(assert (> n 0))
(assert (> m 0))

(assert (in_range n x))
(assert (in_range (+ n m) c))

(assert two_to_the_is_ok)

(assert (or (<= c (intshl (+ n m) 1 (- n 1))) (>= c (intshl (+ n m) (intnot (+ n m ) 0) (- n 1)))))

;precondition:
(assert (= (intnot (+ n m) (intshl (+ n m) (intnot (+ n m) 0) (- n 1))) (- (intshl (+ n m) 1 (- n 1)) 1) ))


; b - the bv
; b_w - its length
; i - the second argument to sign_extend
(define-fun int_sign_extend ((b_w Int) (b Int) (i Int)) Int (ite (< b (intshl b_w 1 (- b_w 1))) b (intor (+ b_w i) (intshl (+ b_w i) (intnot (+ b_w i) 0) b_w) b )))

(define-fun left () Bool (< (int_sign_extend n x m) c))
(define-fun right () Bool (< x (intextract (+ n m) (- n 1) 0 c)))
