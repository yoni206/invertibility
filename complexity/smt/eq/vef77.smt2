(set-logic BV)
(declare-fun s () (_ BitVec 77))
(declare-fun t () (_ BitVec 77))

(define-fun udivtotal ((a (_ BitVec 77)) (b (_ BitVec 77))) (_ BitVec 77)
  (ite (= b (_ bv0 77)) (bvnot (_ bv0 77)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 77)) (b (_ BitVec 77))) (_ BitVec 77)
  (ite (= b (_ bv0 77)) a (bvurem a b))
)
(define-fun min () (_ BitVec 77)
  (bvnot (bvlshr (bvnot (_ bv0 77)) (_ bv1 77)))
)
(define-fun max () (_ BitVec 77)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 77)) (t (_ BitVec 77))) Bool (= (bvand (bvshl (bvnot (_ bv0000 77)) s) t) t))

(define-fun l ((x (_ BitVec 77)) (s (_ BitVec 77)) (t (_ BitVec 77))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 77))) (l x s t)))
  (=> (exists ((x (_ BitVec 77))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
