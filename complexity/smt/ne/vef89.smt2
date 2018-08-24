(set-logic BV)
(declare-fun s () (_ BitVec 89))
(declare-fun t () (_ BitVec 89))

(define-fun udivtotal ((a (_ BitVec 89)) (b (_ BitVec 89))) (_ BitVec 89)
  (ite (= b (_ bv0 89)) (bvnot (_ bv0 89)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 89)) (b (_ BitVec 89))) (_ BitVec 89)
  (ite (= b (_ bv0 89)) a (bvurem a b))
)
(define-fun min () (_ BitVec 89)
  (bvnot (bvlshr (bvnot (_ bv0 89)) (_ bv1 89)))
)
(define-fun max () (_ BitVec 89)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 89)) (t (_ BitVec 89))) Bool (not (= (bvor (bvshl (_ bv7 89) s) t) (_ bv0 89))))

(define-fun l ((x (_ BitVec 89)) (s (_ BitVec 89)) (t (_ BitVec 89))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 89))) (l x s t)))
  (=> (exists ((x (_ BitVec 89))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
