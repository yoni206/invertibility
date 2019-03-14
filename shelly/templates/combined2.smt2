;helper functions for intor and intand. a and b should be 0 or 1.
(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))
(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))
(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))

(declare-fun intor (Int Int Int) Int)

(define-fun full_def_or ((k Int)) Bool (forall ((a Int) (b Int)) 
(!
(=> (and (> k 0) (in_range k a) (in_range k b))
(= (intor k a b) (+ (ite (> k 1) (intor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))
:pattern ((instantiate_me a) (instantiate_me b)))
))

(define-fun or_max1 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a (intmax k)) (intmax k))) :pattern ((instantiate_me a))) ))
(define-fun or_max2 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a 0) a)) :pattern ((instantiate_me a)) )))
(define-fun or_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a a) a)) :pattern ((instantiate_me a))) ))
(define-fun excluded_middle ((k Int)) Bool (forall ((a Int)) (!(=> (and (> k 0) (in_range k a)) (and (= (intor k (intnot k a) a) (intmax k)) (= (intor k a (intnot k a)) (intmax k))  )) :pattern ((instantiate_me a)) )))
(define-fun or_difference1 ((k Int)) Bool (forall ((a Int) (b Int) (c Int)) (! (=> 
(and (distinct a b)  
      (> k 0)
      (in_range k a)
      (in_range k b)
      (in_range k c)
) 
(or (distinct (intor k a c) b) (distinct (intor k b c) a))) :pattern ((instantiate_me a) (instantiate_me b) (instantiate_me c))) ))
(define-fun or_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intor k a b) (intor k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))
(define-fun or_ranges ((k Int)) Bool (forall ((a Int) (b Int)) 
(!(and
  (=>           
    (and
      (> k 0)
      (in_range k a)
      (in_range k b)
    )
    (and
      (in_range k (intor k a b))
      (>= (intor k a b) a) 
      (>= (intor k a b) b) )
    )) :pattern ((instantiate_me a) (instantiate_me b)))
))
(define-fun or_is_ok ((k Int)) Bool (and 
(full_def_or k)
(or_max1 k) 
(or_max2 k) 
(or_ide k)
(excluded_middle k) 
(or_sym k) 
(or_difference1 k)
(or_ranges k)
))

(declare-fun intand (Int Int Int) Int)

;complete axiomatization of bitwise and
(define-fun full_def_and ((k Int)) Bool (forall ((a Int) (b Int)) 
(!
(=> (and (> k 0) (in_range k a) (in_range k b))
(= (intand k a b) (+ (ite (> k 1) (intand (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))
:pattern ((instantiate_me a) (instantiate_me b)))
))

;partial axiomatization of bitwise and, with quantifiers

(define-fun and_max1 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k a (intmax k)) a)) :pattern ((instantiate_me a))) ))
(define-fun and_max2 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k 0 a) 0   )) :pattern ((instantiate_me a))) ))
(define-fun and_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k a a) a)) :pattern ((instantiate_me a))) ))
(define-fun rule_of_contradiction ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a))  (= (intand k (intnot k a) a) 0 )) :pattern ((instantiate_me a))) ))
(define-fun and_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intand k a b) (intand k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))
(define-fun and_difference1 ((k Int)) Bool (forall ((a Int) (b Int) (c Int)) (! (=> 
(and (distinct a b) 
      (> k 0)
      (in_range k a) 
      (in_range k b) 
      (in_range k c) 
) 
(or (distinct (intand k a c) b) (distinct (intand k b c) a))) :pattern ((instantiate_me a) (instantiate_me b) (instantiate_me c))) ))
(define-fun and_ranges ((k Int)) Bool (forall ((a Int) (b Int)) 
(!(and
  (=>           
    (and 
      (> k 0)
      (in_range k a )
      (in_range k b )
    )
    (and
      (in_range k (intand k a b))
      (<= (intand k a b) a) 
      (<= (intand k a b) b) )
    )) :pattern ((instantiate_me a) (instantiate_me b) ))
))

(define-fun and_is_ok ((k Int)) Bool (and 
(full_def_and k)
(and_max1 k) 
(and_max2 k) 
(and_ide k)
(rule_of_contradiction k) 
(and_sym k) 
(and_difference1 k)
(and_ranges k)
))


(declare-fun intxor_dec (Int Int Int) Int)

(define-fun full_def_xor ((k Int)) Bool (forall ((a Int) (b Int)) 
(!
(=> (and (> k 0) (in_range k a) (in_range k b))
(= (intxor k a b) (+ (ite (> k 1) (intxor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (two_to_the (- k 1)) (intxor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))
:pattern ((instantiate_me a) (instantiate_me b)))
))

(define-fun xor_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a) ) (= (intxor k a a) 0)) :pattern ((instantiate_me a))) ))
(define-fun xor_flip ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intxor k a (intnot k a)) (intmax k))) :pattern ((instantiate_me a))) ))
(define-fun xor_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intxor k a b) (intxor k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))
(define-fun xor_ranges ((k Int)) Bool (forall ((a Int) (b Int)) 
(!(and
  (=>           
    (and 
      (> k 0)
      (in_range k a)
      (in_range k b)
    )
     (in_range k (intxor k a b))
    )) :pattern ((instantiate_me a) (instantiate_me b)))
))

(define-fun xor_is_ok ((k Int)) Bool (and 
  (full_def_xor k)
  (xor_ide k)
  (xor_flip k)
  (xor_sym k)
  (xor_ranges k)
))

