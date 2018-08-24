(set-logic BV)
(declare-fun s () (_ BitVec 98))
(declare-fun t () (_ BitVec 98))

(define-fun udivtotal ((a (_ BitVec 98)) (b (_ BitVec 98))) (_ BitVec 98)
  (ite (= b (_ bv0 98)) (bvnot (_ bv0 98)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 98)) (b (_ BitVec 98))) (_ BitVec 98)
  (ite (= b (_ bv0 98)) a (bvurem a b))
)
(define-fun min () (_ BitVec 98)
  (bvnot (bvlshr (bvnot (_ bv0 98)) (_ bv1 98)))
)
(define-fun max () (_ BitVec 98)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 98)) (t (_ BitVec 98))) Bool (= (bvand (bvshl (bvnot (_ bv0000 98)) s) t) t))

(define-fun l ((x (_ BitVec 98)) (s (_ BitVec 98)) (t (_ BitVec 98))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 98))) (l x s t)))
  (=> (exists ((x (_ BitVec 98))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
