(set-logic UFNIA)

(define-fun-rec pow ((a Int)(b Int)) Int 
    (ite (<= b 0) 
         1 
         (* a (pow a (- b 1)))))

(define-fun divtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow 2 (- k 1 )) 1) (div a b) ))
(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun shl ((k Int) (a Int) (b Int)) Int (modtotal (* a (pow 2 b)) (pow 2 (- k 1))))
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool ( < (shl k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (distinct t 0)
 )

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (pow 2 (- k 1)))))

(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (range_assumptions k s t) (=> (SC k s t) (exists ((x Int)) (and (in_range k x) (l k x s t))))))
(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (range_assumptions k s t) (=> (exists ((x Int)) (and (in_range k x) (l k x s t))) (SC k s t) )))

(define-fun hypothesis1 () Bool (forall ((k Int) (s Int) (t Int)) (left_to_right k s t)))
(define-fun hypothesis2 () Bool (forall ((k Int) (s Int) (t Int)) (right_to_left k s t)))

(assert (not hypothesis2))
;(declare-fun s () Int)
;(declare-fun t () Int)
;(declare-fun k () Int)
;(declare-fun x () Int)
;(assert (and (range_assumptions k s t) (and (in_range k x) (l k x s t)) (not (SC k s t))))
(check-sat)
