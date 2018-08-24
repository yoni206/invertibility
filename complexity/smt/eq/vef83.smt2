(set-logic BV)
(declare-fun s () (_ BitVec 83))
(declare-fun t () (_ BitVec 83))

(define-fun udivtotal ((a (_ BitVec 83)) (b (_ BitVec 83))) (_ BitVec 83)
  (ite (= b (_ bv0 83)) (bvnot (_ bv0 83)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 83)) (b (_ BitVec 83))) (_ BitVec 83)
  (ite (= b (_ bv0 83)) a (bvurem a b))
)
(define-fun min () (_ BitVec 83)
  (bvnot (bvlshr (bvnot (_ bv0 83)) (_ bv1 83)))
)
(define-fun max () (_ BitVec 83)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 83)) (t (_ BitVec 83))) Bool (= (bvand (bvshl (bvnot (_ bv0000 83)) s) t) t))

(define-fun l ((x (_ BitVec 83)) (s (_ BitVec 83)) (t (_ BitVec 83))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 83))) (l x s t)))
  (=> (exists ((x (_ BitVec 83))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
