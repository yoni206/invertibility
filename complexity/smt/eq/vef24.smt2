(set-logic BV)
(declare-fun s () (_ BitVec 24))
(declare-fun t () (_ BitVec 24))

(define-fun udivtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) (bvnot (_ bv0 24)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) a (bvurem a b))
)
(define-fun min () (_ BitVec 24)
  (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24)))
)
(define-fun max () (_ BitVec 24)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 24)) (t (_ BitVec 24))) Bool (= (bvand (bvshl (bvnot (_ bv0000 24)) s) t) t))

(define-fun l ((x (_ BitVec 24)) (s (_ BitVec 24)) (t (_ BitVec 24))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 24))) (l x s t)))
  (=> (exists ((x (_ BitVec 24))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)