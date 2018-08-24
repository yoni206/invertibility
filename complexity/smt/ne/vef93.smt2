(set-logic BV)
(declare-fun s () (_ BitVec 93))
(declare-fun t () (_ BitVec 93))

(define-fun udivtotal ((a (_ BitVec 93)) (b (_ BitVec 93))) (_ BitVec 93)
  (ite (= b (_ bv0 93)) (bvnot (_ bv0 93)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 93)) (b (_ BitVec 93))) (_ BitVec 93)
  (ite (= b (_ bv0 93)) a (bvurem a b))
)
(define-fun min () (_ BitVec 93)
  (bvnot (bvlshr (bvnot (_ bv0 93)) (_ bv1 93)))
)
(define-fun max () (_ BitVec 93)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 93)) (t (_ BitVec 93))) Bool (not (= (bvor (bvshl (_ bv7 93) s) t) (_ bv0 93))))

(define-fun l ((x (_ BitVec 93)) (s (_ BitVec 93)) (t (_ BitVec 93))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 93))) (l x s t)))
  (=> (exists ((x (_ BitVec 93))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
