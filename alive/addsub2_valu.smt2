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
;(define-fun two_to_the ((b Int)) Int (two_to_the_def b))
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
;(define-fun two_to_the_is_ok () Bool two_to_the_is_ok_rec)
(define-fun two_to_the_is_ok () Bool two_to_the_is_ok_qf)

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

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 2) (in_range k s) (in_range k t)))

(declare-fun k () Int)
(declare-fun C () Int)
(declare-fun x () Int)

(assert (<= k 11))
(assert (instantiate_me k))
(assert (instantiate_me C))
(assert (instantiate_me x))

(assert two_to_the_is_ok)
(assert (two_to_the_is_ok_for k))
(assert (two_to_the_is_ok_for C))
(assert (two_to_the_is_ok_for x))
(assert (range_assumptions k C x))


(assert (= C (intsub k k 1)))
(assert (< C k))
(assert (distinct (intsub k 0 (intlshr k x C)) (intashr k x C)))

(check-sat)
