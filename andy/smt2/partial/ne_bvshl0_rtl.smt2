(set-logic UFNIA)

;power stuff
(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok ((b Int)) Bool (and  (= (two_to_the 0) 1) (= (two_to_the 1) 2) (= (two_to_the 2) 4) (forall ((i Int) (j Int)) (=> (and (>= i 0) (>= j 0) (<= i b) (<= j b)) (and (=> (<= i j) (<= (two_to_the i) (two_to_the j))) (=> (< i j) (< (two_to_the i) (two_to_the j))))))))
(define-fun two_to_the_is_ok_unbounded () Bool (forall ((b Int)) (=> (>= b 0) (two_to_the_is_ok b)) ) )

;required operations
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (two_to_the b)) (two_to_the k)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Main course: l and SC       ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intshl k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (distinct t 0) (< s k))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;   range functions        ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))



(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(declare-fun x () Int)
(assert (forall ((x0 Int) (y0 Int)) (=> (and (<= x0 y0) (>= x0 0) (>= y0 0)) (= (two_to_the y0) (* (two_to_the x0) (two_to_the (- y0 x0)))))))
;(assert (forall ((k0 Int) (s0 Int) (x0 Int)) (=> (distinct (mod (* x0 (two_to_the s0)) (two_to_the k0)) 0) (< s0 k0)) ))
;(assert (forall ((x0 Int)) (=> (distinct (mod (* x0 (two_to_the s)) (two_to_the k)) 0) (< s k))))
;(assert (=> (distinct (mod (* x (two_to_the s)) (two_to_the k)) 0) (< s k)))
(assert (range_assumptions k s t))
(assert (in_range k x))
(assert (and (two_to_the_is_ok k) (two_to_the_is_ok s) (two_to_the_is_ok t)))
(assert two_to_the_is_ok_unbounded)

(assert (and (l k x s t) (not (SC k s t))))

(check-sat)

