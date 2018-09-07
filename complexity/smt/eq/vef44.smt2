(set-logic BV)
(declare-fun s () (_ BitVec 44))
(declare-fun t () (_ BitVec 44))

(define-fun udivtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) (bvnot (_ bv0 44)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) a (bvurem a b))
)
(define-fun min () (_ BitVec 44)
  (bvnot (bvlshr (bvnot (_ bv0 44)) (_ bv1 44)))
)
(define-fun max () (_ BitVec 44)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 44)) (t (_ BitVec 44))) Bool (= (bvand (bvshl (bvnot (_ bv0000 44)) s) t) t))

(define-fun l ((x (_ BitVec 44)) (s (_ BitVec 44)) (t (_ BitVec 44))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 44))) (l x s t)))
  (=> (exists ((x (_ BitVec 44))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)