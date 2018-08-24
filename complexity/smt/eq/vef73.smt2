(set-logic BV)
(declare-fun s () (_ BitVec 73))
(declare-fun t () (_ BitVec 73))

(define-fun udivtotal ((a (_ BitVec 73)) (b (_ BitVec 73))) (_ BitVec 73)
  (ite (= b (_ bv0 73)) (bvnot (_ bv0 73)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 73)) (b (_ BitVec 73))) (_ BitVec 73)
  (ite (= b (_ bv0 73)) a (bvurem a b))
)
(define-fun min () (_ BitVec 73)
  (bvnot (bvlshr (bvnot (_ bv0 73)) (_ bv1 73)))
)
(define-fun max () (_ BitVec 73)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 73)) (t (_ BitVec 73))) Bool (= (bvand (bvshl (bvnot (_ bv0000 73)) s) t) t))

(define-fun l ((x (_ BitVec 73)) (s (_ BitVec 73)) (t (_ BitVec 73))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 73))) (l x s t)))
  (=> (exists ((x (_ BitVec 73))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
