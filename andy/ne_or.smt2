(set-logic UFNIA)

(declare-fun instantiate_me (Int) Bool)
(declare-fun intmax (Int) Int)
(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))
(define-fun not_constants ((k Int)) Bool (and (= (intnot k 0) (intmax k)) (= (intnot k (intmax k)) 0 ) ))
(define-fun not_diff ((k Int)) Bool (forall ((a Int)) (!(and (instantiate_me a) (distinct (intnot k a) a)) :pattern ((instantiate_me a)))))
(define-fun not_is_ok ((k Int)) Bool (and (not_constants k) (not_diff k)))

(declare-fun intor (Int Int Int) Int)
(define-fun or_max1 ((k Int)) Bool (forall ((a Int)) (!(and (instantiate_me a)   (= (intor k a (intmax k)) (intmax k))) :pattern ((instantiate_me a))) ))
(define-fun or_max2 ((k Int)) Bool (forall ((a Int)) (!(and (instantiate_me a) (= (intor k 0 a) a)   (= (intor k a 0) a)) :pattern ((instantiate_me a))) ))
(define-fun excluded_middle ((k Int)) Bool (forall ((a Int)) (!(and (instantiate_me a) (= (intor k (intnot k a) a) (intmax k)) (= (intor k a (intnot k a)) (intmax k))  ) :pattern ((instantiate_me a))) ))
(define-fun or_difference1 ((k Int)) Bool (forall ((a Int) (b Int) (c Int)) (!(and (instantiate_me a) (instantiate_me b) (instantiate_me c) (=> (distinct a b) (or (distinct (intor k a c) b) (distinct (intor k b c) a)))) :pattern ((instantiate_me a) (instantiate_me b) (instantiate_me c))) ))
(define-fun or_difference2 ((k Int)) Bool (forall ((a Int) (b Int) ) (!(and (instantiate_me a) (instantiate_me b)  (=> (distinct a 0) (distinct (intor k a b) (intnot k a) ))) :pattern ((instantiate_me a) (instantiate_me b) )) ))
(define-fun or_sym ((k Int)) Bool (forall ((a Int) (b Int)) (!(and (instantiate_me a) (instantiate_me b) (= (intor k a b) (intor k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))
(define-fun or_is_ok ((k Int)) Bool (and 
(or_max1 k) 
(or_max2 k) 
(excluded_middle k) 
(or_sym k) 
(or_difference1 k)
))



(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intor k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (distinct s (intmax k)) (distinct t (intmax k))))

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (<= x (intmax k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(assert (instantiate_me k))
(assert (instantiate_me s))
(assert (instantiate_me t))

(define-fun left_to_right ((k Int) (s Int) (t Int)) Bool (=> (SC k s t) (l k (intnot k t) s t)))
(define-fun assertion_ltr () Bool (not (left_to_right k s t)))


(assert (range_assumptions k s t))
(assert (or_is_ok k))
(assert (not_is_ok k))

(assert assertion_ltr)

(check-sat)
