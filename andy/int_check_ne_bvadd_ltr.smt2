(set-logic UFNIA)

;power stuff
(declare-fun two_to_the (Int) Int)
;approximate axiomatization of power, with bounded quantifiers
(define-fun two_to_the_is_ok_partial ((b Int)) Bool
(and
(= (two_to_the 0) 1)
(= (two_to_the 1) 2)
(= (two_to_the 2) 4)
(forall ((i Int) (j Int))
(=>
(and (>= i 0) (>= j 0) (<= i b) (<= j b))
(and
(=> (<= i j) (<= (two_to_the i) (two_to_the j))) ;weak monotinicity
(=> (< i j) (< (two_to_the i) (two_to_the j))) ;strong monotinicity
(forall ((x Int)) (=> (>= x 0) (=> (distinct (mod (* x (two_to_the i)) (two_to_the j)) 0) (< i j)))) ;fun fact
)
)
)
)
)

(define-fun two_to_the_is_ok ((b Int)) Bool (two_to_the_is_ok_partial b))
(define-fun two_to_the_is_ok_unbounded () Bool (forall ((b Int)) (=> (>= b 0) (two_to_the_is_ok b)) ) )

;other definitions
(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))

;l and SC
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intadd k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true)

;conditional inverse
(define-fun inv ((k Int) (s Int) (t Int)) Int (intnot k (intadd k s t)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (l k (inv k s t) s t)))
(define-fun assertion_ltr () Bool (not (left_to_right k s t)))

;range helpers (everything between 0 and 2^k)
(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

;original assertions
(assert (range_assumptions k s t))
(assert (and (two_to_the_is_ok k) (two_to_the_is_ok s) (two_to_the_is_ok t)  ))
(assert two_to_the_is_ok_unbounded)
(assert assertion_ltr)

;new cool lemma: 2^k-1 is never even, as long as k>0
;(assert (distinct (- (two_to_the k) 1) (* 2 t)))
(assert (forall ((x Int)) (=> (>= x 0) (distinct (- (two_to_the k) 1) (* 2 x))) ))
;(assert (forall ((k0 Int)) (=> (>= k0 1) (distinct (- (two_to_the k0) 1) (* 2 t) ))))


(check-sat)
