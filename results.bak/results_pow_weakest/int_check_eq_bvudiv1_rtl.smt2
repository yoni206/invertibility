(set-logic UFNIA)

(declare-fun pow (Int Int) Int) ;(pow(a,b) = a^b)

(define-fun divtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow 2 k) 1) (div a b) ))
(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (modtotal (* a (pow 2 b)) (pow 2 k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (modtotal (divtotal k a (pow 2 b)) (pow 2 k)))
;(define-fun intashr ((k Int) (a Int) (b Int)) Int (modtotal (divtotal k a (pow 2 b)) (pow 2 k)))
;(define-fun intnot ((k Int) (a Int)) Int ())
(define-fun intneg ((k Int) (a Int)) Int (- (pow 2 k) a))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow 2 m)) b))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool (= (mod (divtotal k s x) (pow 2 k)) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (= (mod (divtotal k s (mod (divtotal k s t) (pow 2 k))) (pow 2 k)) t)

)

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (pow 2 k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (range_assumptions k s t) (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (l k x s t))))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (range_assumptions k s t) (=> (exists ((x Int)) (and (in_range k x) (l k x s t))) (SC k s t) )))



(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_rtl () Bool (not (right_to_left k s t)))

(assert assertion_rtl)

(check-sat)


