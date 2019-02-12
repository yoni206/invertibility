(set-logic UFNIA)

(declare-fun k () Int)

(declare-fun two_to_the (Int) Int) 
(define-fun two_to_the_is_ok_full () Bool (and (= (two_to_the 0) 1) (forall ((i Int)) (=> (> i 0) (= (two_to_the i) (* (two_to_the (- i 1)) 2))) )))

(declare-fun intor (Int Int Int) Int)

(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))
(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
(define-fun bitof ((k Int) (l Int) (a Int)) Int (intextract k l l a))
(define-fun lsb ((k Int) (a Int)) Int (bitof k 0 a))
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))
(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))

(define-fun or_is_ok_full ((k Int)) Bool (forall ((a Int) (b Int)) 
(and
  (= (intor 1 a b) (intor_helper (lsb k a) (lsb k b)))
  (=>           
      (> k 1)
      (= (intor k a b) (+ (intor (- k 1) a b) (* (two_to_the (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))
    )))
))

(define-fun or_max2 ((k Int)) Bool (forall ((a Int)) (and (= (intor k 0 a) a)   (= (intor k a 0) a)) ))

(assert (> k 0))
(assert two_to_the_is_ok_full)
(assert (or_is_ok_full k))
(assert (not (or_max2 k)))
(check-sat)
