(set-logic UFNIA)

(declare-fun k () Int)

(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) )))

(declare-fun intand (Int Int Int) Int)

(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
(define-fun bitof ((k Int) (l Int) (a Int)) Int (intextract k l l a))
(define-fun lsb ((k Int) (a Int)) Int (bitof k 0 a))
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))
(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))

(define-fun and_is_ok_full ((k Int)) Bool (forall ((a Int) (b Int)) 
(and
  (= (intand 1 a b) (intand_helper (lsb k a) (lsb k b)))
  (=>           
      (> k 1)
      (= (intand k a b) (+ (intand (- k 1) a b) (* (two_to_the (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))
    )))
))

(define-fun and_ranges ((k Int)) Bool (forall ((a Int) (b Int)) 
(and
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
    )) )
)

(assert (> k 0))
(assert two_to_the_is_ok_full)
(assert (and_is_ok_full k))
(assert (not (and_ranges k)))
(check-sat)
