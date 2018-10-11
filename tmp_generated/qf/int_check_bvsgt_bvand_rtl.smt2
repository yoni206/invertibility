(set-logic UFNIA)
;;;;;;;;;;;;;;;;;;;;;;;;;
;    power definitions  ;
;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition


;declaration that will be axiomatized
(declare-fun two_to_the_dec (Int) Int)

;choose your power!
(define-fun two_to_the ((b Int)) Int (two_to_the_dec b))

;complete axiomatization of power


;approximate axiomatization of power, with bounded quantifiers


;approximate axiomatization of power, no quantifers
(define-fun two_to_the_is_ok_qf ((b Int)) Bool (and (= (two_to_the 0) 1) (= (two_to_the 1) 2) (= (two_to_the 2) 4) (=> (and (> b 2)) (and (> (two_to_the b) 4) (= (two_to_the b) (* (two_to_the (- b 1)) 2)) ))  ) )

;trivial axiomatization of power, in case the recursive definition is used
(define-fun two_to_the_is_ok_rec ((b Int) ) Bool true)

;choose version of power properties
(define-fun two_to_the_is_ok ((b Int)) Bool (two_to_the_is_ok_qf b))

;unbounded quantification:


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;     other functions     ;
;     without and/or      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;mins and maxs. intmax and intmin are maximum and minimum positive values of a bitvector of size k.
(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intmin ((k Int)) Int 0)

;div and mod
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (two_to_the k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))


;bvneg and bvnot
(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (two_to_the k) a) (two_to_the k)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))

;intmins is the positive value of the bitvector that represents the minimal signed value. similarly for intmaxs. s is for signed.
(define-fun intmins ((k Int)) Int (two_to_the (- k 1)))
(define-fun intmaxs ((k Int)) Int (intnot k (intmins k)))

;extract
(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))

;easy translations
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (two_to_the b)) (two_to_the k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (two_to_the b)) (two_to_the k)))
(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (intextract k (- k 1) (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (two_to_the m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (two_to_the k)))
(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))

;signed business
;Given an integer x s.t. 0<= x <= (2^k)-1, x can be represented by a bitvector v, so that x is the unsigned interpretation of v. now, v also has a signed interpretation, call it y. Then (unsigned_to_signed k x)=y.
(define-fun unsigned_to_signed ((k Int) (x Int)) Int (- (* 2 (intextract k (- k 2) 0 x)) x))
(define-fun intslt ((k Int) (a Int) (b Int)) Bool (< (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsgt ((k Int) (a Int) (b Int)) Bool (> (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsle ((k Int) (a Int) (b Int)) Bool (<= (unsigned_to_signed k a) (unsigned_to_signed k b)) )
(define-fun intsge ((k Int) (a Int) (b Int)) Bool (>= (unsigned_to_signed k a) (unsigned_to_signed k b)) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;    utility functions for and/or  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;helper functions for intor and intand. a and b should be 0 or 1.
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))

;the l bit in the representatino of a as a k-width bitvector
(define-fun bitof ((k Int) (l Int) (a Int)) Int (intextract k l l a))
(define-fun lsb ((k Int) (a Int)) Int (bitof k 0 a))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         bitwise or definitions       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition of or


;declaration that will be axiomatized
(declare-fun intor_dec (Int Int Int) Int)


;choose your or!
(define-fun intor ((k Int) (a Int) (b Int)) Int (intor_dec k a b))


;complete axiomatization of bitwise or


;partial axiomatization of bitwise or, with quantifiers


;partial axiomatization of bitwise or - quantifier free
(define-fun or_is_ok_qf ((k Int) (a Int) ) Bool
(and
(= (intor k 0 a) a)
(= (intor k a 0) a)
(= (intor k (intmax k) a) (intmax k))
(= (intor k a (intmax k)) (intmax k))
)
)


;trivial axiomatization if recursive definition was chosen
(define-fun or_is_ok_rec ((k Int) (a Int) ) Bool true)

;choose version of properties for or
(define-fun or_is_ok ((k Int) (a Int)) Bool (or_is_ok_qf k a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         bitwise and definitions       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition of and


;declaration that will be axiomatized
(declare-fun intand_dec (Int Int Int) Int)


;choose your and!
(define-fun intand ((k Int) (a Int) (b Int)) Int (intand_dec k a b))

;complete axiomatization of bitwise and


;partial axiomatization of bitwise and, with quantifiers


;partial axiomatization of bitwise and - quantifier free
(define-fun and_is_ok_qf ((k Int) (a Int) ) Bool
(and
(= (intand k 0 a) 0)
(= (intand k a 0) 0)
(= (intand k (intmax k) a) a)
(= (intand k a (intmax k)) a)
)
)

;trivial axiomatization for bitwise and - for when recursive definition is used
(define-fun and_is_ok_rec ((k Int) (a Int) ) Bool true)


;choose version of properties
(define-fun and_is_ok ((k Int) (a Int)) Bool (and_is_ok_qf k a))

(define-fun and_or_are_ok ((k Int) (a Int)) Bool (and (and_is_ok k a) (or_is_ok k a)))



;unbounded quantification:




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (intsgt k (intand k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (intslt k t (intand k s (intmaxs k)))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

;;;;;;;;;;;;;;;;;;;;;;;
;more place-holders   ;
;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

;skolemized x for the right-to-left direction
(declare-fun x0 () Int)


;It is better to directly negate right_to_left in order to avoid quantification
(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))


(define-fun assertion_rtl () Bool (not_right_to_left k s t))




(assert (range_assumptions k s t))
(assert (in_range k x0))
(assert (and (two_to_the_is_ok k) (two_to_the_is_ok s) (two_to_the_is_ok t)  ))
(assert (two_to_the_is_ok x0))
(assert (and (and_or_are_ok k s) (and_or_are_ok k t) ))
(assert (and_or_are_ok k x0))




(assert assertion_rtl)

(check-sat)