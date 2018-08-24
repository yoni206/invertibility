(set-logic BV)
(declare-fun s () (_ BitVec 70))
(declare-fun t () (_ BitVec 70))

(define-fun udivtotal ((a (_ BitVec 70)) (b (_ BitVec 70))) (_ BitVec 70)
  (ite (= b (_ bv0 70)) (bvnot (_ bv0 70)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 70)) (b (_ BitVec 70))) (_ BitVec 70)
  (ite (= b (_ bv0 70)) a (bvurem a b))
)
(define-fun min () (_ BitVec 70)
  (bvnot (bvlshr (bvnot (_ bv0 70)) (_ bv1 70)))
)
(define-fun max () (_ BitVec 70)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 70)) (t (_ BitVec 70))) Bool (not (= (bvor (bvshl (_ bv7 70) s) t) (_ bv0 70))))

(define-fun l ((x (_ BitVec 70)) (s (_ BitVec 70)) (t (_ BitVec 70))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 70))) (l x s t)))
  (=> (exists ((x (_ BitVec 70))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
