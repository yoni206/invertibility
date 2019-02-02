(set-logic UFNIA)

(declare-fun two_to_the (Int) Int)
(define-fun intmax ((k Int)) Int (- (two_to_the k) 1))

(declare-fun intand (Int Int Int) Int)
(define-fun and_is_ok_for ((k Int) (a Int) ) Bool
(and
(= (intand k a 0) 0)
)
)

(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (< x (two_to_the k))))

(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (distinct (intand k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool (or (distinct s 0) (distinct t 0)))

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)
(declare-fun x0 () Int)

(define-fun right_to_left ((k Int) (s Int) (t Int)) Bool (=> (exists ((x Int)) (and (in_range k x) (and_is_ok_for k x) (l k x s t))) (SC k s t) ))
(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))
(define-fun assertion_rtl () Bool (not_right_to_left k s t))


(assert (and_is_ok_for k x0))
(assert assertion_rtl)

(check-sat)
