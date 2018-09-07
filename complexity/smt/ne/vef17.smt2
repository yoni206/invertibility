(set-logic BV)
(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)
(define-fun min () (_ BitVec 17)
  (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17)))
)
(define-fun max () (_ BitVec 17)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 17)) (t (_ BitVec 17))) Bool (not (= (bvor (bvshl (_ bv7 17) s) t) (_ bv0 17))))

(define-fun l ((x (_ BitVec 17)) (s (_ BitVec 17)) (t (_ BitVec 17))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 17))) (l x s t)))
  (=> (exists ((x (_ BitVec 17))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)