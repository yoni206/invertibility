(set-logic UFNIA)
(declare-fun two_to_the (Int) Int) 

;approximate axiomatization of power, no quantifers
(define-fun two_to_the_is_ok ((b Int)) Bool (and (= (two_to_the 0) 1) (= (two_to_the 1) 2) (= (two_to_the 2) 4) (=> (and (> b 2)) (and (> (two_to_the b) 4) (= (two_to_the b) (* (two_to_the (- b 1)) 2)) ))  ) )

;unbounded quantification:
(define-fun two_to_the_is_ok_unbounded () Bool (forall ((b Int)) (=> (>= b 0) (two_to_the_is_ok b)) ) )

(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))

(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (<= (intadd k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (l k x s t)))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (two_to_the_is_ok x) (l k x s t))) (SC k s t) ))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_rtl () Bool (not (right_to_left k s t)))


(assert (range_assumptions k s t))
(assert (and (two_to_the_is_ok k) (two_to_the_is_ok s) (two_to_the_is_ok t)))
(assert two_to_the_is_ok_unbounded)

(assert assertion_ltr)

(check-sat)

