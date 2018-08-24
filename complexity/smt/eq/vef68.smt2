(set-logic BV)
(declare-fun s () (_ BitVec 68))
(declare-fun t () (_ BitVec 68))

(define-fun udivtotal ((a (_ BitVec 68)) (b (_ BitVec 68))) (_ BitVec 68)
  (ite (= b (_ bv0 68)) (bvnot (_ bv0 68)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 68)) (b (_ BitVec 68))) (_ BitVec 68)
  (ite (= b (_ bv0 68)) a (bvurem a b))
)
(define-fun min () (_ BitVec 68)
  (bvnot (bvlshr (bvnot (_ bv0 68)) (_ bv1 68)))
)
(define-fun max () (_ BitVec 68)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 68)) (t (_ BitVec 68))) Bool (= (bvand (bvshl (bvnot (_ bv0000 68)) s) t) t))

(define-fun l ((x (_ BitVec 68)) (s (_ BitVec 68)) (t (_ BitVec 68))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 68))) (l x s t)))
  (=> (exists ((x (_ BitVec 68))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
