(set-logic QF_UFNIA)
(declare-fun two_to_the (Int) Int)
(define-fun bitof ((k Int) (l Int) (a Int)) Int (mod (div a (two_to_the l)) 2))
(define-fun int_all_but_msb ((k Int) (a Int)) Int (mod a (two_to_the (- k 1))))
(declare-fun intand (Int Int Int) Int)
(declare-fun intor (Int Int Int) Int)
(declare-fun intxor (Int Int Int) Int)
(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intmin ((k Int)) Int 0)
(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (<= x (intmax k))))
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (two_to_the k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (two_to_the k) a) (two_to_the k)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intmins ((k Int)) Int (two_to_the (- k 1)))
(define-fun intmaxs ((k Int)) Int (intnot k (intmins k)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (two_to_the b)) (two_to_the k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (two_to_the b)) (two_to_the k)))
(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (bitof k (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (two_to_the m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (two_to_the k)))
(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))
(define-fun unsigned_to_signed ((k Int) (x Int)) Int (- (* 2 (int_all_but_msb k x)) x))
(define-fun intslt ((k Int) (a Int) (b Int)) Bool (< (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsgt ((k Int) (a Int) (b Int)) Bool (> (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsle ((k Int) (a Int) (b Int)) Bool (<= (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsge ((k Int) (a Int) (b Int)) Bool (>= (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun base_cases () Bool (and (= (two_to_the 0) 1) (= (two_to_the 1) 2) (= (two_to_the 2) 4) (= (two_to_the 3) 8) ) )
;qf axioms
(define-fun two_to_the_ax () Bool base_cases)
(define-fun and_ax ((k Int)) Bool true)
(define-fun or_ax ((k Int)) Bool true)
(define-fun xor_ax ((k Int)) Bool true)
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (= (intand k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (= (intand k t s) t))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)


;<BEGIN_RTL>
;skolemized x for the right-to-left direction
(declare-fun x0 () Int)
(assert (in_range k x0))

;(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (l k x s t))) (SC k s t) ))
;It is better to directly negate right_to_left in order to be able to use the skolem x0
(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))

(define-fun assertion_rtl () Bool (not_right_to_left k s t))
;<END_RTL>

;general assertions
(assert (range_assumptions k s t))
(assert two_to_the_ax)
(assert (and_ax k))


(assert assertion_rtl)

(check-sat)