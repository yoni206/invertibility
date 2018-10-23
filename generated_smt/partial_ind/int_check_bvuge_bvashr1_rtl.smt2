(set-logic UFNIA)

;dummy function to be used in quantifier instantiation patterns
(declare-fun instantiate_me (Int) Bool)

;;;;;;;;;;;;;;;;;;;;;;;;;
;    power definitions  ;
;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition
(define-fun-rec two_to_the_def ((b Int)) Int
(ite (<= b 0)
1
(* 2 (two_to_the_def (- b 1)))))

;declaration that will be axiomatized
(declare-fun two_to_the_dec (Int) Int)

;choose your power!
(define-fun two_to_the ((b Int)) Int (two_to_the_dec b))

;complete axiomatization of power
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (!(and (instantiate_me i) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2)))) :pattern ((instantiate_me i))) )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;    partial axiomatization of power  ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;some fixed values
(define-fun base_cases () Bool
(and
(= (two_to_the 0) 1)
(= (two_to_the 1) 2)
(= (two_to_the 2) 4)
(= (two_to_the 3) 8)
)
)

;weak-monotinicity
(define-fun weak_monotinicity () Bool
(forall ((i Int) (j Int))
(=>
(and (>= i 0) (>= j 0) )
(=> (<= i j) (<= (two_to_the i) (two_to_the j)))
)
)
)

;strong-monotinicity
(define-fun strong_monotinicity () Bool
(forall ((i Int) (j Int))
(=>
(and (>= i 0) (>= j 0) )
(=> (< i j) (< (two_to_the i) (two_to_the j)))
)
)
)

;if 2^i mod 2^j is not 0, then i<j
(define-fun modular_power () Bool
(forall ((i Int) (j Int) (x Int))
(!(and
(instantiate_me i)
(instantiate_me j)
(instantiate_me x)
(=>
(and (>= i 0) (>= j 0) (>= x 0) (distinct (mod (* x (two_to_the i)) (two_to_the j)) 0))
(< i j)
)
) :pattern ((instantiate_me i) (instantiate_me j) (instantiate_me x)))
)
)

;2^k -1 is never even, provided that k != 0
(define-fun never_even () Bool
(forall ((k Int) (x Int))
(!(and
(instantiate_me k)
(instantiate_me x)
(=>
(and (>= k 1) (>= x 0))
(distinct (- (two_to_the k) 1) (* 2 x))
)
) :pattern ((instantiate_me k) (instantiate_me x)))
)
)

(define-fun two_to_the_is_ok_partial () Bool
(and
base_cases
weak_monotinicity
strong_monotinicity
modular_power
never_even
)
)

;quantifier-free axiomatization of power
(define-fun two_to_the_is_ok_qf () Bool base_cases)

;quantifier-free helper, to use on specific variables
(define-fun two_to_the_is_ok_for ((b Int)) Bool
(=> (and (> b 3)) (and (> (two_to_the b) 8) (= (two_to_the b) (* (two_to_the (- b 1)) 2)) ))
)

;trivial axiomatization of power, in case the recursive definition is used
(define-fun two_to_the_is_ok_rec () Bool true)

;choose version of power properties
(define-fun two_to_the_is_ok () Bool two_to_the_is_ok_partial)

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

;other easu functions
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (two_to_the b)) (two_to_the k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (two_to_the b)) (two_to_the k)))
(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (intextract k (- k 1) (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (two_to_the m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (two_to_the k)))
(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))

;signed business
;Given an integer x s.t. 0<= x <= (2^k)-1, x can be represented by a bitvector v,
;so that x is the unsigned interpretation of v.
;now, v also has a signed interpretation, call it y.
;Then (unsigned_to_signed k x) := y.
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
(define-fun-rec intor_def ((k Int) (a Int) (b Int)) Int
(ite (<= k 1)
(intor_helper (lsb k a) (lsb k b))
(+ (intor_def (- k 1) a b) (* (two_to_the (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))

;declaration that will be axiomatized
(declare-fun intor_dec (Int Int Int) Int)

;choose your or!
(define-fun intor ((k Int) (a Int) (b Int)) Int (intor_dec k a b))

;complete axiomatization of bitwise or
(define-fun or_is_ok_full ((k Int)) Bool (forall ((a Int) (b Int))
(!(and
(instantiate_me a)
(instantiate_me b)
(= (intor 1 a b) (intor_helper (lsb k a) (lsb k b)))
(=>
(and
(> k 1)
(>= a 0)
(>= b 0)
(<= a (intmax k))
(<= b (intmax k))
)
(and
(= (intor k a b) (+ (intor (- k 1) a b) (* (two_to_the (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b)))))
))) :pattern ((instantiate_me a) (instantiate_me b)))
))

;partial axiomatization of bitwise or, with quantifiers

(define-fun or_is_ok_partial ((k Int)) Bool (forall ((a Int) (b Int))
(!(and
(instantiate_me a)
(instantiate_me b)
(= (intor 1 a b) (intor_helper (lsb k a) (lsb k b)))
(=>
(and
(>= a 0)
(>= b 0)
(<= a (intmax k))
(<= b (intmax k))
)
(and
(>= (intor k a b) 0)
(<= (intor k a b ) (intmax k))
(>= (intor k a b) a)
(>= (intor k a b) b) )
)) :pattern ((instantiate_me a) (instantiate_me b)))
))



;partial axiomatization of bitwise or - quantifier free
(define-fun or_is_ok_qf ((k Int)) Bool true)

(define-fun or_is_ok_for ((k Int) (a Int) ) Bool
(and
(= (intor k 0 a) a)
(= (intor k a 0) a)
(= (intor k (intmax k) a) (intmax k))
(= (intor k a (intmax k)) (intmax k))
)
)

;trivial axiomatization if recursive definition was chosen
(define-fun or_is_ok_rec ((k Int)  ) Bool true)

;choose version of properties for or
(define-fun or_is_ok ((k Int)) Bool (or_is_ok_partial k))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         bitwise and definitions       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition of and
(define-fun-rec intand_def ((k Int) (a Int) (b Int)) Int
(ite (<= k 1)
(intand_helper (lsb k a) (lsb k b))
(+ (intand_def (- k 1) a b) (* (two_to_the (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))

;declaration that will be axiomatized
(declare-fun intand_dec (Int Int Int) Int)

;choose your and!
(define-fun intand ((k Int) (a Int) (b Int)) Int (intand_dec k a b))

;complete axiomatization of bitwise and
(define-fun and_is_ok_full ((k Int)) Bool (forall ((a Int) (b Int))
(!(and
(instantiate_me a)
(instantiate_me b)
(= (intand 1 a b) (intand_helper (lsb k a) (lsb k b)))
(=>
(and
(>= a 0)
(>= b 0)
(<= a (intmax k))
(<= b (intmax k))
)
(and
(= (intand k a b) (+ (intand (- k 1) a b) (* (two_to_the (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b)))))
))) :pattern ((instantiate_me a) (instantiate_me b)))
))

;partial axiomatization of bitwise and, with quantifiers
(define-fun and_is_ok_partial ((k Int)) Bool (forall ((a Int) (b Int))
(!(and
(instantiate_me a)
(instantiate_me b)
(= (intand 1 a b) (intand_helper (lsb k a) (lsb k b)))
(=>
(and
(>= a 0)
(>= b 0)
(<= a (intmax k))
(<= b (intmax k))
)
(and
(>= (intand k a b) 0)
(<= (intand k a b ) (intmax k))
(<= (intand k a b) a)
(<= (intand k a b) b) )
)) :pattern ((instantiate_me a) (instantiate_me b) ))
))

(define-fun and_is_ok_qf ((k Int)) Bool true)

(define-fun and_is_ok_for ((k Int) (a Int) ) Bool
(and
(= (intand k 0 a) 0)
(= (intand k a 0) 0)
(= (intand k (intmax k) a) a)
(= (intand k a (intmax k)) a)
)
)

;trivial axiomatization for bitwise and - for when recursive definition is used
(define-fun and_is_ok_rec ((k Int) ) Bool true)

;choose version of properties
(define-fun and_is_ok ((k Int)) Bool (and_is_ok_partial k))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (>= (intashr k s x) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (not (and (< s (intnot k s)) (< s t)))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(assert (instantiate_me k))
(assert (instantiate_me s))
(assert (instantiate_me t))

;extra, harmless qf assertions
(define-fun everything_is_ok_for ((k Int) (a Int)) Bool (and (two_to_the_is_ok_for a) (two_to_the_is_ok_for k) (and_is_ok_for k a) (or_is_ok_for k a) ))
(assert (everything_is_ok_for k k))
(assert (everything_is_ok_for k s))
(assert (everything_is_ok_for k t))



;<BEGIN_RTL>
;skolemized x for the right-to-left direction
(declare-fun x0 () Int)
(assert (instantiate_me x0))
(assert (in_range k x0))

(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (everything_is_ok_for k x) (l k x s t))) (SC k s t) ))

;It is better to directly negate right_to_left in order to be able to use the skolem x0
(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))

(define-fun assertion_rtl () Bool (not_right_to_left k s t))
(define-fun assertion_rtl_ind () Bool (not (=> (right_to_left k s t) (right_to_left (+ k 1) s t))))
(assert (everything_is_ok_for k x0))
;<END_RTL>

;general assertions
(assert (range_assumptions k s t))
(assert two_to_the_is_ok)




(assert assertion_rtl_ind)

(check-sat)