;original BV
;(set-logic BV)
;(declare-fun s () (_ BitVec 4))
;(declare-fun t () (_ BitVec 4))
;(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool (or (distinct t (_ bv0 4)) (distinct s (_ bv0 4))))
;(define-fun l ( (x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool (distinct (bvmul x s) t))
;(define-fun left_to_right () Bool (=> (SC s t) (exists ((x (_ BitVec 4))) (l x s t))))
;(define-fun right_to_left () Bool (=> (exists ((x (_ BitVec 4))) (l x s t)) (SC s t)))
;(assert (not (and left_to_right right_to_left)))


;new NIA
(set-logic NIA)
(define-fun SC ((s Int) (t Int)) Bool (or (distinct t 0) (distinct s 0)))
(define-fun l ((n Int) (x Int) (s Int) (t Int)) Bool (distinct (mod (* x s) n ) t))
(define-fun in_range ((n Int) (x Int)) Bool (and (>= x 0) (< x n)))
(define-fun range_assumptions ((n Int) (s Int) (t Int)) Bool (and (> n 0) (in_range n s) (in_range n t)))
(define-fun left_to_right ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (SC s t) (exists ((x Int)) (and (in_range n x) (l n x s t))))))
(define-fun right_to_left ((n Int) (s Int) (t Int)) Bool (=> (range_assumptions n s t) (=> (exists ((x Int)) (and (in_range n x) (l n x s t))) (SC s t) )))
(define-fun equivalence ((n Int) (s Int) (t Int)) Bool (and (left_to_right n s t) (right_to_left n s t)))
(define-fun hypothesis () Bool (forall ((n Int) (s Int) (t Int)) (equivalence n s t)))
;(assert (not hypothesis)) ;z3 timeout

(define-fun hypothesis1 () Bool (forall ((n Int) (s Int) (t Int)) (left_to_right n s t)))
(define-fun hypothesis2 () Bool (forall ((n Int) (s Int) (t Int)) (right_to_left n s t)))
(push)
(assert (not hypothesis2)) ;z3 unsat
(check-sat)
(pop)
(push)
(assert (not hypothesis1)) ;z3 timeout
(check-sat)
