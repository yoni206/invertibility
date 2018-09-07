(set-logic UFNIA)
;;;;;;;;;;;;;;;;;;;;;;;;;
;    power definitions  ;
;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition
(define-fun-rec pow_def ((a Int) (b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow_def a (- b 1)))))

;declaration that will be axiomatized
(declare-fun pow_dec (Int Int) Int) 

;complete axiomatization of power
(define-fun pow_is_ok_full ((a Int) (b Int)) Bool (and (= (pow_dec a 0) 1) (forall ((i Int)) (=> (and (> i 0) (<= i b)) (= (pow_dec a i) (* (pow_dec a (- i 1)) a)))) ))

;approximate axiomatization of power, with quantifiers
(define-fun pow_is_ok_partial ((a Int) (b Int)) Bool (forall ((i Int) (j Int)) (and (=> (and (>= i 0) (>= j 0) (<= i a) (<= j b) ) (and (= (pow_dec i 0) 0) (= (pow_dec 1 j) 1) (= (pow_dec i 1) i) (>= (pow_dec i j) 0) (<= (pow_dec i j) (pow_dec a b)))) (=> (and (> i 1) (> j 1)) (> (pow_dec i j) i)))))

;approximate axiomatization of power, no quantifers
(define-fun pow_is_ok_qf ((a Int) (b Int)) Bool (and (>= a 0) (>= b 0) (= (pow_dec 0 1) 0) (= (pow_dec 1 1) 1) (= (pow_dec 1 0) 1) (= (pow_dec a 0) 1) (= (pow_dec a 1) a) (= (pow_dec 1 b) 1) (=> (and (> a 1) (> b 1)) (and (> (pow_dec a b) a) (= (pow_dec a b) (* (pow_dec a (- b 1)) a)) ))  ) )

;trivial axiomatization of power, in case the recursive definition is used
(define-fun pow_is_ok_rec ((a Int) (b Int) ) Bool true)

;choose version of power
(define-fun pow ((a Int) (b Int)) Int (pow_dec a b))
(define-fun pow_is_ok ((a Int) (b Int)) Bool (pow_is_ok_partial a b))



;;;;;;;;;;;;;;;;;;;;;;;;;;;
;     other functions     ;
;     without and/or      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

;mins and maxs. intmax and intmin are maximum and minimum positive values of a bitvector of size k.
(define-fun intmax ((k Int)) Int (- (pow 2 k) 1))
(define-fun intmin ((k Int)) Int 0)

;div and mod
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow 2 k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))


;bvneg and bvnot 
(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (pow 2 k) a) (pow 2 k)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))

;intmins is the positive value of the bitvector that represents the minimal signed value. similarly for intmaxs. s is for signed.
(define-fun intmins ((k Int)) Int (pow 2 (- k 1)))
(define-fun intmaxs ((k Int)) Int (intnot k (intmins k)))

;extract 
(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int (mod (div a (pow 2 j)) (pow 2 (+ (- i j) 1))))

;easy translations
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow 2 b)) (pow 2 k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (pow 2 b)) (pow 2 k)))
(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (intextract k (- k 1) (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow 2 m)) b))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow 2 k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (pow 2 k)))
(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))



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
        (+ (intor_def (- k 1) a b) (* (pow 2 (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))

;declaration that will be axiomatized
(declare-fun intor_dec (Int Int Int) Int)

;complete axiomatization of bitwise or
(define-fun or_is_ok_full ((k Int) (x Int)) Bool (forall ((m Int) (a Int) (b Int)) 
(and
  (=>           
    (and 
      (> m 1)
      (<= m k)
      (>= a 0)
      (>= b 0)
      (<= a (intmax k))
      (<= b (intmax k))
    )
    (and
      (= (intor_dec 1 a b) (intor_helper (lsb k a) (lsb k b)))
      (= (intor_dec m a b) (+ (intor_dec (- m 1) a b) (* (pow 2 (- m 1)) (intor_helper (bitof k (- m 1) a) (bitof k (- m 1) b)))))
    )))))

;partial axiomatization of bitwise or, with quantifiers
(define-fun or_is_ok_partial ((k Int) (x Int)) Bool (forall ((m Int) (a Int) (b Int)) 
(and
  (=>           
    (and 
      (> m 1)
      (<= m k)
      (>= a 0)
      (>= b 0)
      (<= a (intmax k))
      (<= b (intmax k))
    )
    (and
      (= (intor_dec 1 a b) (intor_helper (lsb k a) (lsb k b)))
      (>= (intor_dec m a b) 0) 
      (<= (intor_dec m a b ) (intmax k)) 
      (>= (intor_dec m a b) a) 
      (>= (intor_dec m a b) b) )
    ))))

;partial axiomatization of bitwise or - quantifier free
(define-fun or_is_ok_qf ((k Int) (a Int) ) Bool 
(and
        (= (intor_dec k 0 a) a)
        (= (intor_dec k a 0) a)
        (= (intor_dec k (intmax k) a) (intmax k))
        (= (intor_dec k a (intmax k)) (intmax k))
    )
)

(define-fun or_is_ok_rec ((k Int) (a Int) ) Bool true)

;choose version
(define-fun intor ((k Int) (a Int) (b Int)) Int (intor_dec k a b))
(define-fun or_is_ok ((k Int) (a Int)) Bool (or_is_ok_partial k a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         bitwise and definitions       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;recursive definition of and
(define-fun-rec intand_def ((k Int) (a Int) (b Int)) Int
    (ite (<= k 1)
        (intand_helper (lsb k a) (lsb k b))
        (+ (intand_def (- k 1) a b) (* (pow 2 (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))

;declaration that will be axiomatized
(declare-fun intand_dec (Int Int Int) Int)

;complete axiomatization of bitwise and
(define-fun and_is_ok_full ((k Int) (x Int)) Bool (forall ((m Int) (a Int) (b Int)) 
(and
  (=>           
    (and 
      (> m 1)
      (<= m k)
      (>= a 0)
      (>= b 0)
      (<= a (intmax k))
      (<= b (intmax k))
    )
    (and
      (= (intand_dec 1 a b) (intand_helper (lsb k a) (lsb k b)))
      (= (intand_dec m a b) (+ (intand_dec (- m 1) a b) (* (pow 2 (- m 1)) (intand_helper (bitof k (- m 1) a) (bitof k (- m 1) b)))))
    )))))

;partial axiomatization of bitwise and, with quantifiers
(define-fun and_is_ok_partial ((k Int) (x Int)) Bool (forall ((m Int) (a Int) (b Int)) 
(and
  (=>           
    (and 
      (> m 1)
      (<= m k)
      (>= a 0)
      (>= b 0)
      (<= a (intmax k))
      (<= b (intmax k))
    )
    (and
      (= (intand_dec 1 a b) (intand_helper (lsb k a) (lsb k b)))
      (>= (intand_dec m a b) 0) 
      (<= (intand_dec m a b ) (intmax k)) 
      (<= (intand_dec m a b) a) 
      (<= (intand_dec m a b) b) )
    ))))

;partial axiomatization of bitwise and - quantifier free
(define-fun and_is_ok_qf ((k Int) (a Int) ) Bool 
(and
        (= (intand_dec k 0 a) 0)
        (= (intand_dec k a 0) 0)
        (= (intand_dec k (intmax k) a) a)
        (= (intand_dec k a (intmax k)) a)
    )
)

;trivial axiomatization for bitwise and - for when recursive definition is used
(define-fun and_is_ok_rec ((k Int) (a Int) ) Bool true)


;choose version
(define-fun intand ((k Int) (a Int) (b Int)) Int (intand_dec k a b))
(define-fun and_is_ok ((k Int) (a Int)) Bool (and_is_ok_partial k a))

(define-fun and_or_are_ok ((k Int) (a Int)) Bool (and (and_is_ok k a) (or_is_ok k a)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (<= (intshl k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (pow 2 k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (and_or_are_ok k x) (l k x s t)))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (and_or_are_ok k x) (l k x s t))) (SC k s t) ))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_rtl () Bool (not (right_to_left k s t)))
(define-fun assertion_ltr_ind () Bool (not (=> (left_to_right k s t) (left_to_right (+ k 1) s t))))
(define-fun assertion_rtl_ind () Bool (not (=> (right_to_left k s t) (right_to_left (+ k 1) s t))))


(assert (range_assumptions k s t))
(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
(assert (and (and_or_are_ok k s) (and_or_are_ok k t)))
(assert assertion_rtl)

(check-sat)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;         stuff            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;alternative final commands for analyzing sat instances of rtl
;(declare-fun x0 () Int)
;(assert (range_assumptions k s t))
;(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
;(assert (and (in_range k x0) (pow_is_ok 2 x0) (l k x0 s t) (not (SC k s t))))
;(check-sat)
;(get-value (k s t x0))
