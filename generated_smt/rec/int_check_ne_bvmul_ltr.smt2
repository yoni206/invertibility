(set-logic UFNIA)

(define-fun-rec two_to_the ((b Int)) Int
(ite (<= b 0)
1
(* 2 (two_to_the (- b 1)))))


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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intmul k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (distinct t 0) (distinct s 0))
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


;<BEGIN_LTR>
(define-fun inv_syntax_g ((k Int) (s Int) (t Int)) Int (intshl k (intmaxs k) t))
(define-fun l_part ((k Int) (s Int) (t Int)) Bool (or (exists ((x Int)) (and (in_range k x)  (l k x s t))) (and (in_range k (inv_syntax_g k s t))  (l k (inv_syntax_g k s t) s t))))
(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (l_part k s t)))
(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_ltr_ind () Bool (not (=> (left_to_right k s t) (left_to_right (+ k 1) s t))))
;<END_LTR>

;general assertions
(assert (range_assumptions k s t))

(assert assertion_ltr)

(check-sat)
(get-value (k s t (inv_syntax_g k s t) ))
