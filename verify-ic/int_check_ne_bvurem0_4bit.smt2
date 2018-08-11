;original BV
;(set-logic BV)
;(declare-fun s () (_ BitVec 4))
;(declare-fun t () (_ BitVec 4))
;(define-fun uremtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4) (ite (= b (_ bv0 4)) a (bvurem a b)))
;(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool (or (distinct s (_ bv1 4)) (distinct t (_ bv0 4))))
;(define-fun l ( (x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool (distinct (uremtotal x s) t))
;(define-fun left_to_right () Bool (=> (SC s t) (exists ((x (_ BitVec 4))) (l x s t))))
;(define-fun right_to_left () Bool (=> (exists ((x (_ BitVec 4))) (l x s t)) (SC s t)))
;(assert (not (and left_to_right right_to_left)))

;new NIA
(set-logic NIA)
(define-fun modtotal ((a Int) (b Int)) Int (ite (= b 0) a (mod a b)))
(define-fun SC ((s Int) (t Int)) Bool (or (distinct s 1) (distinct t 0)))
(define-fun l ((x Int) (s Int) (t Int)) Bool (distinct ( modtotal x s) t))
(define-fun in_range ( (x Int)) Bool (>= x 0))
(define-fun range_assumptions ((s Int) (t Int)) Bool (and (in_range s) (in_range t)))
(define-fun left_to_right ( (s Int) (t Int)) Bool (=> (range_assumptions s t) (=> (SC s t) (exists ((x Int)) (and (in_range x) (l x s t))))))
(define-fun right_to_left ( (s Int) (t Int)) Bool (=> (range_assumptions s t) (=> (exists ((x Int)) (and (in_range x) (l x s t))) (SC s t) )))
(define-fun equivalence ( (s Int) (t Int)) Bool (and (left_to_right s t) (right_to_left s t)))
(define-fun hypothesis () Bool (forall ( (s Int) (t Int)) (equivalence s t)))
(assert (not hypothesis)) ;z3 unsat
(check-sat)
