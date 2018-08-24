(set-logic BV)
(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)
(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 35)) (t (_ BitVec 35))) Bool (= (bvand (bvshl (bvnot (_ bv0000 35)) s) t) t))

(define-fun l ((x (_ BitVec 35)) (s (_ BitVec 35)) (t (_ BitVec 35))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (l x s t)))
  (=> (exists ((x (_ BitVec 35))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
