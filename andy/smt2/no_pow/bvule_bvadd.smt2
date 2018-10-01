(set-logic UFNIA)
(define-fun intmodtotal ((n Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))

;n is meant to be 2^k for some k. but this is an over approximation
(define-fun intadd ((n Int) (a Int) (b Int) ) Int (intmodtotal n (+ a b) n))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((n Int) (x Int) (s Int) (t Int)) Bool  (<= (intadd n x s) t))
(define-fun SC ((n Int) (s Int) (t Int)) Bool true

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((n Int) (x Int)) Bool (and (>= x 0) (< x n)))
(define-fun range_assumptions ((n Int) (s Int) (t Int)) Bool (and (>= n 2) (in_range n s) (in_range n t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun left_to_right ((n Int) (s Int) (t Int)) Bool (=> (SC n s t) (exists ((x Int)) (and (in_range n x) (l n x s t)))))
(define-fun right_to_left ((n Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range n x)  (l n x s t))) (SC n s t) ))

(declare-fun n () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun assertion_ltr () Bool (not (left_to_right n s t)))
(define-fun assertion_rtl () Bool (not (right_to_left n s t)))


(assert (range_assumptions n s t))

(assert assertion_ltr)

(check-sat)

