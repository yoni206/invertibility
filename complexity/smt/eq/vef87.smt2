(set-logic BV)
(declare-fun s () (_ BitVec 87))
(declare-fun t () (_ BitVec 87))

(define-fun udivtotal ((a (_ BitVec 87)) (b (_ BitVec 87))) (_ BitVec 87)
  (ite (= b (_ bv0 87)) (bvnot (_ bv0 87)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 87)) (b (_ BitVec 87))) (_ BitVec 87)
  (ite (= b (_ bv0 87)) a (bvurem a b))
)
(define-fun min () (_ BitVec 87)
  (bvnot (bvlshr (bvnot (_ bv0 87)) (_ bv1 87)))
)
(define-fun max () (_ BitVec 87)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 87)) (t (_ BitVec 87))) Bool (= (bvand (bvshl (bvnot (_ bv0000 87)) s) t) t))

(define-fun l ((x (_ BitVec 87)) (s (_ BitVec 87)) (t (_ BitVec 87))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 87))) (l x s t)))
  (=> (exists ((x (_ BitVec 87))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
