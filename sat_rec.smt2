(declare-fun instantiate_me (Int) Bool)

(define-fun-rec two_to_the ((b Int)) Int
(ite (<= b 0)
1
(* 2 (two_to_the (- b 1)))))

(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))

(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (two_to_the k)))

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))
(define-fun range_assumptions ((k Int) (s Int) (t Int)) Bool (and (>= k 1) (in_range k s) (in_range k t)))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (= (intadd k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true

)

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)

(assert (instantiate_me k))
(assert (instantiate_me s))
(assert (instantiate_me t))

(assert (range_assumptions k s t))


(define-fun l_part ((k Int) (s Int) (t Int)) Bool (exists ((x Int)) (and  (in_range k x) (instantiate_me x) (l k x s t))))

(assert (SC k s t))
(assert (not (l_part k s t)))

(check-sat)
