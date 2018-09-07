(set-logic BV)
(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)
(define-fun min () (_ BitVec 45)
  (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45)))
)
(define-fun max () (_ BitVec 45)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 45)) (t (_ BitVec 45))) Bool (= (bvand (bvshl (bvnot (_ bv0000 45)) s) t) t))

(define-fun l ((x (_ BitVec 45)) (s (_ BitVec 45)) (t (_ BitVec 45))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 45))) (l x s t)))
  (=> (exists ((x (_ BitVec 45))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)