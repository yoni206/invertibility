(set-logic BV)
(declare-fun s () (_ BitVec 94))
(declare-fun t () (_ BitVec 94))

(define-fun udivtotal ((a (_ BitVec 94)) (b (_ BitVec 94))) (_ BitVec 94)
  (ite (= b (_ bv0 94)) (bvnot (_ bv0 94)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 94)) (b (_ BitVec 94))) (_ BitVec 94)
  (ite (= b (_ bv0 94)) a (bvurem a b))
)
(define-fun min () (_ BitVec 94)
  (bvnot (bvlshr (bvnot (_ bv0 94)) (_ bv1 94)))
)
(define-fun max () (_ BitVec 94)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 94)) (t (_ BitVec 94))) Bool (not (= (bvor (bvshl (_ bv7 94) s) t) (_ bv0 94))))

(define-fun l ((x (_ BitVec 94)) (s (_ BitVec 94)) (t (_ BitVec 94))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 94))) (l x s t)))
  (=> (exists ((x (_ BitVec 94))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
