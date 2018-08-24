(set-logic BV)
(declare-fun s () (_ BitVec 81))
(declare-fun t () (_ BitVec 81))

(define-fun udivtotal ((a (_ BitVec 81)) (b (_ BitVec 81))) (_ BitVec 81)
  (ite (= b (_ bv0 81)) (bvnot (_ bv0 81)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 81)) (b (_ BitVec 81))) (_ BitVec 81)
  (ite (= b (_ bv0 81)) a (bvurem a b))
)
(define-fun min () (_ BitVec 81)
  (bvnot (bvlshr (bvnot (_ bv0 81)) (_ bv1 81)))
)
(define-fun max () (_ BitVec 81)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 81)) (t (_ BitVec 81))) Bool (= (bvand (bvshl (bvnot (_ bv0000 81)) s) t) t))

(define-fun l ((x (_ BitVec 81)) (s (_ BitVec 81)) (t (_ BitVec 81))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 81))) (l x s t)))
  (=> (exists ((x (_ BitVec 81))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
