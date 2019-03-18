(set-logic QF_UFNIA)
(declare-fun pow2 (Int) Int)
(declare-fun intand (Int Int Int) Int)
(declare-fun intor (Int Int Int) Int)
(declare-fun intxor (Int Int Int) Int)
(define-fun bitof ((k Int) (l Int) (a Int)) Int (mod (div a (pow2 l)) 2))
(define-fun int_all_but_msb ((k Int) (a Int)) Int (mod a (pow2 (- k 1))))
(define-fun intmax ((k Int)) Int (- (pow2 k) 1))
(define-fun intmin ((k Int)) Int 0)
(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (<= x (intmax k))))
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow2 k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (pow2 k) a) (pow2 k)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intmins ((k Int)) Int (pow2 (- k 1)))
(define-fun intmaxs ((k Int)) Int (intnot k (intmins k)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow2 b)) (pow2 k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (pow2 b)) (pow2 k)))
(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (bitof k (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow2 m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow2 k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (pow2 k)))
(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))
(define-fun unsigned_to_signed ((k Int) (x Int)) Int (- (* 2 (int_all_but_msb k x)) x))
(define-fun intslt ((k Int) (a Int) (b Int)) Bool (< (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsgt ((k Int) (a Int) (b Int)) Bool (> (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsle ((k Int) (a Int) (b Int)) Bool (<= (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsge ((k Int) (a Int) (b Int)) Bool (>= (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun pow2_base_cases () Bool (and (= (pow2 0) 1) (= (pow2 1) 2) (= (pow2 2) 4) (= (pow2 3) 8) ) )
;qf axioms
(define-fun pow2_ax () Bool pow2_base_cases)
(define-fun and_ax ((k Int)) Bool true)
(define-fun or_ax ((k Int)) Bool true)
(define-fun xor_ax ((k Int)) Bool true)
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intshl k s x) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (distinct s 0) (distinct t 0)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

;<BEGIN_LTR>
(define-fun inv ((k Int) (s Int) (t Int)) Int t)
(define-fun l_part ((k Int) (s Int) (t Int)) Bool (l k ( inv k s t) s t))
(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (l_part k s t)))
(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
;<END_LTR>


;general assertions
(assert (>= k 1))
(assert (in_range k s))
(assert (in_range k t))
(assert pow2_ax)



(assert assertion_ltr)

(check-sat)