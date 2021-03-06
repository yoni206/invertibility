(set-info :smt-lib-version 2.6)
(set-logic UFNIA)
(set-info :source |
Generated by: Yoni Zohar
Generated on: 2019-03-18
Application: verifying invertibility conditions
Target solver: CVC4, z3, vampire
Publications: "Solving Quantified Bit-Vectors using Invertibility Conditions" by A. Niemetz, M. Preiner, A. Reynolds, C. Barrett, and C. Tinelli, CAV 2018.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unknown)

(declare-fun pow2 (Int) Int)
(declare-fun intand (Int Int Int) Int)
(declare-fun intor (Int Int Int) Int)
(declare-fun intxor (Int Int Int) Int)
(define-fun bitof ((k Int) (l Int) (a Int)) Int (mod (div a (pow2 l)) 2))
(define-fun int_all_but_msb ((k Int) (a Int)) Int (mod a (pow2 (- k 1))))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))
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
(define-fun pow2_ind_def () Bool (and (= (pow2 0) 1) (forall ((i Int)) (=> (> i 0) (= (pow2 i) (* (pow2 (- i 1)) 2)))  )))
(define-fun and_ind_def ((k Int)) Bool (forall ((a Int) (b Int)) (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intand k a b) (+ (ite (> k 1) (intand (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
(define-fun or_ind_def ((k Int)) Bool (forall ((a Int) (b Int))   (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intor k a b) (+ (ite (> k 1) (intor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
(define-fun xor_ind_def ((k Int)) Bool (forall ((a Int) (b Int))   (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intxor k a b) (+ (ite (> k 1) (intxor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intxor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
;full axioms
(define-fun pow2_ax () Bool pow2_ind_def)
(define-fun and_ax ((k Int)) Bool (and_ind_def k))
(define-fun or_ax ((k Int)) Bool (or_ind_def k))
(define-fun xor_ax ((k Int)) Bool (xor_ind_def k))
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (<= (intmodtotal k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true)

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

;<BEGIN_LTR>
(define-fun inv ((k Int) (s Int) (t Int)) Int s)
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