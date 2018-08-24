(set-logic BV)
(declare-fun s () (_ BitVec 40))
(declare-fun t () (_ BitVec 40))

(define-fun udivtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) (bvnot (_ bv0 40)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) a (bvurem a b))
)
(define-fun min () (_ BitVec 40)
  (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40)))
)
(define-fun max () (_ BitVec 40)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 40)) (t (_ BitVec 40))) Bool (= (bvand (bvshl (bvnot (_ bv0000 40)) s) t) t))

(define-fun l ((x (_ BitVec 40)) (s (_ BitVec 40)) (t (_ BitVec 40))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 40))) (l x s t)))
  (=> (exists ((x (_ BitVec 40))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
