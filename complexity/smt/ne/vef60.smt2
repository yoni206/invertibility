(set-logic BV)
(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)
(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 60)) (t (_ BitVec 60))) Bool (not (= (bvor (bvshl (_ bv7 60) s) t) (_ bv0 60))))

(define-fun l ((x (_ BitVec 60)) (s (_ BitVec 60)) (t (_ BitVec 60))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 60))) (l x s t)))
  (=> (exists ((x (_ BitVec 60))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
