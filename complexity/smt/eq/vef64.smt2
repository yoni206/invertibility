(set-logic BV)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)
(define-fun min () (_ BitVec 64)
  (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64)))
)
(define-fun max () (_ BitVec 64)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 64)) (t (_ BitVec 64))) Bool (= (bvand (bvshl (bvnot (_ bv0000 64)) s) t) t))

(define-fun l ((x (_ BitVec 64)) (s (_ BitVec 64)) (t (_ BitVec 64))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 64))) (l x s t)))
  (=> (exists ((x (_ BitVec 64))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
