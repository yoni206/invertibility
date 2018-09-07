(set-logic UFNIA)

#various definitions for problematic functions
(define-fun-rec pow_def ((a Int) (b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))
(declare-fun pow_dec (Int Int) Int) 
(define-fun pow_is_ok_full ((a Int) (b Int)) Bool (and (= (pow_dec a 0) 1) (forall ((i Int)) (=> (and (> i 0) (<= i b)) (= (pow_dec a i) (* (pow_dec a (- i 1)) a)))) ))

(define-fun pow ((a Int) (b Int)) Int <pow>)


(define-fun intmax ((k Int)) Int (- (pow 2 k) 1))
(define-fun intmin ((k Int)) Int 0)
(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow 2 k) 1) (div a b) ))
(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow 2 b)) (pow 2 k)))
(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (pow 2 b)) (pow 2 k)))
(define-fun intneg ((k Int) (a Int)) Int (- (pow 2 k) a))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow 2 m)) b))
(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int (mod (div a (pow 2 j)) (pow 2 (+ (- i j) 1))))

(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (intextract k (- k 1) (- k 1) a) 0) (intlshr a b) (intnot k (intlshr (intnot a) b))))
(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow 2 k)))
(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (pow 2 k)))

(declare-fun intor (Int Int Int) Int)
(declare-fun intand (Int Int Int) Int)

(define-fun or_is_ok ((k Int)) Bool 
(and
  (forall ((i Int) (j Int))
    (=>
      (and
        (>= i 0)
        (>= j 0)
        (<= i (intmax k)) 
        (<= j (intmax k)) 
      )
      (and
        (>= (intor k i j) 0)
        (<= (intor k i j) (intmax k))
      )
    )
  )
  (forall ((i Int))
    (=>
      (and
        (>= i 0)
        (<= i (intmax k)) 
      )
      (and
        (= (intor k 0 i) i)
        (= (intor k i 0) i)
        (= (intor k (intmax k) i) (intmax k))
        (= (intor k i (intmax k)) (intmax k))
      )
    )
  )
))


(define-fun and_is_ok ((k Int)) Bool 
(and
  (forall ((i Int) (j Int))
    (=>
      (and
        (>= i 0)
        (>= j 0)
        (<= i (intmax k)) 
        (<= j (intmax k)) 
      )
      (and
        (>= (intand k i j) 0)
        (<= (intand k i j) (intmax k))
      )
    )
  )
  (forall ((i Int))
    (=>
      (and
        (>= i 0)
        (<= i (intmax k)) 
      )
      (and
        (= (intand k 0 i) 0)
        (= (intand k i 0) 0)
        (= (intand k (intmax k) i) i)
        (= (intand k i (intmax k)) i)
      )
    )
  )
))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool <l>)
(define-fun SC ((k Int) (s Int) (t Int)) Bool <SC>
)

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (pow 2 k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (l k x s t)))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (pow_is_ok 2 x) (l k x s t))) (SC k s t) ))


(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)



(define-fun assertion_ltr () Bool (not (left_to_right k s t)))
(define-fun assertion_rtl () Bool (not (right_to_left k s t)))
(define-fun assertion_ltr_ind () Bool (not (=> (left_to_right k s t) (left_to_right (+ k 1) s t))))
(define-fun assertion_rtl_ind () Bool (not (=> (right_to_left k s t) (right_to_left (+ k 1) s t))))


(assert (range_assumptions k s t))
(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
(assert (and (and_is_ok k) (or_is_ok k)))
(assert <assertion>)

(check-sat)



;alternative final commands for analyzing sat instances of rtl
;(declare-fun x0 () Int)
;(assert (range_assumptions k s t))
;(assert (and (pow_is_ok 2 k) (pow_is_ok 2 s) (pow_is_ok 2 t)))
;(assert (and (in_range k x0) (pow_is_ok 2 x0) (l k x0 s t) (not (SC k s t))))
;(check-sat)
;(get-value (k s t x0))