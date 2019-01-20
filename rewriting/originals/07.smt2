;c^n+m < Rewrite zero_extend(x^n,m)
;--->
;c[n-1:0] < x   if c[n+m-1:n] == 0


(declare-fun x () Int)
(declare-fun c () Int)

(declare-fun n () Int)
(declare-fun m () Int)

(assert (> n 0))
(assert (> m 0))

(assert (in_range n x))
(assert (in_range (+ n m) c))

(assert two_to_the_is_ok)
(assert (= (intextract (+ n m) (- (+ n m) 1) n c ) 0))


(define-fun left () Bool (< c x))
(define-fun right () Bool  (< (intextract (+ n m) (- n 1) 0 c) x))
