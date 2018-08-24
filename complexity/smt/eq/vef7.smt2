(set-logic BV)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))

(define-fun udivtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) (bvnot (_ bv0 7)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) a (bvurem a b))
)
(define-fun min () (_ BitVec 7)
  (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7)))
)
(define-fun max () (_ BitVec 7)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 7)) (t (_ BitVec 7))) Bool (= (bvand (bvshl (bvnot (_ bv0000 7)) s) t) t))

(define-fun l ((x (_ BitVec 7)) (s (_ BitVec 7)) (t (_ BitVec 7))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 7))) (l x s t)))
  (=> (exists ((x (_ BitVec 7))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
