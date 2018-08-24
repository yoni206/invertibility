(set-logic BV)
(declare-fun s () (_ BitVec 90))
(declare-fun t () (_ BitVec 90))

(define-fun udivtotal ((a (_ BitVec 90)) (b (_ BitVec 90))) (_ BitVec 90)
  (ite (= b (_ bv0 90)) (bvnot (_ bv0 90)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 90)) (b (_ BitVec 90))) (_ BitVec 90)
  (ite (= b (_ bv0 90)) a (bvurem a b))
)
(define-fun min () (_ BitVec 90)
  (bvnot (bvlshr (bvnot (_ bv0 90)) (_ bv1 90)))
)
(define-fun max () (_ BitVec 90)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 90)) (t (_ BitVec 90))) Bool (= (bvand (bvshl (bvnot (_ bv0000 90)) s) t) t))

(define-fun l ((x (_ BitVec 90)) (s (_ BitVec 90)) (t (_ BitVec 90))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 90))) (l x s t)))
  (=> (exists ((x (_ BitVec 90))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
