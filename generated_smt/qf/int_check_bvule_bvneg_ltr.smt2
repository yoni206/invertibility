(set-logic UFNIA)

(declare-fun pow (Int Int) Int) ;(pow a b) = a^b
(define-fun pow_is_ok ((a Int) (b Int)) Bool (and (>= a 0) (>= b 0) (= (pow 0 1) 0) (= (pow 1 1) 1) (= (pow 1 0) 1) (= (pow a 0) 1) (= (pow a 1) a) (= (pow 1 b) 1) (=> (and (> a 1) (> b 1)) (and (> (pow a b) a) (= (pow a b) (* (pow a (- b 1)) a)) ))  ) )

(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow 2 k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow 2 b)) (pow 2 k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (pow 2 b)) (pow 2 k)))
(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (pow 2 k) a) (pow 2 k) ))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow 2 m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow 2 k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (pow 2 k)))
(define-fun intmax ((k Int)) Int (- (pow 2 k) 1))
(define-fun intmin ((k Int)) Int 0)

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (<= (intneg k x) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true

)

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (pow 2 k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (l k x s t)))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (l k x s t))) (SC k s t) ))


(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)



(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_rtl () Bool (not (right_to_left k s t)))
(define-fun assertion_ltr_ind () Bool (not (=> (left_to_right k s t) (left_to_right (+ k 1) s t))))
(define-fun assertion_rtl_ind () Bool (not (=> (right_to_left k s t) (right_to_left (+ k 1) s t))))


(assert (range_assumptions k s t))
(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
(assert assertion_ltr)

(check-sat)



;alternative final commands for analyzing sat instances of rtl
;(declare-fun x0 () Int)
;(assert (range_assumptions k s t))
;(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
;(assert (and (in_range k x0) (pow_is_ok 2 x0) (l k x0 s t) (not (SC k s t))))
;(check-sat)
;(get-value (k s t x0))
