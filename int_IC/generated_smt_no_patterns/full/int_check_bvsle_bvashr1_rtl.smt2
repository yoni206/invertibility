(set-logic UFNIA)
(declare-fun two_to_the (Int) Int)
(declare-fun intand (Int Int Int) Int)
(declare-fun intor (Int Int Int) Int)
(declare-fun intxor (Int Int Int) Int)
(define-fun bitof ((k Int) (l Int) (a Int)) Int (mod (div a (two_to_the l)) 2))
(define-fun int_all_but_msb ((k Int) (a Int)) Int (mod a (two_to_the (- k 1))))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))
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
(define-fun two_to_the_ind_def () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2)))  )))
(define-fun and_ind_def ((k Int)) Bool (forall ((a Int) (b Int)) (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intand k a b) (+ (ite (> k 1) (intand (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
(define-fun or_ind_def ((k Int)) Bool (forall ((a Int) (b Int))   (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intor k a b) (+ (ite (> k 1) (intor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
(define-fun xor_ind_def ((k Int)) Bool (forall ((a Int) (b Int))   (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intxor k a b) (+ (ite (> k 1) (intxor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intxor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))  ))
;full axioms
(define-fun two_to_the_ax () Bool two_to_the_ind_def)
(define-fun and_ax ((k Int)) Bool (and_ind_def k))
(define-fun or_ax ((k Int)) Bool (or_ind_def k))
(define-fun xor_ax ((k Int)) Bool (xor_ind_def k))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (intsle k (intashr k s x) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (intsge k t 0) (intsge k t s)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(assert (instantiate_me k))
(assert (instantiate_me s))
(assert (instantiate_me t))


;<BEGIN_RTL>
;skolemized x for the right-to-left direction
(declare-fun x0 () Int)
(assert (instantiate_me x0))
(assert (in_range k x0))

(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))

(define-fun assertion_rtl () Bool (not_right_to_left k s t))
;<END_RTL>

;general assertions
(assert (range_assumptions k s t))
(assert two_to_the_ax)



(assert assertion_rtl)

(check-sat)