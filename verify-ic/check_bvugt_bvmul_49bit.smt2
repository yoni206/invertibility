(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 49))
(declare-fun t () (_ BitVec 49))

(define-fun udivtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) (bvnot (_ bv0 49)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) a (bvurem a b))
)
(define-fun min () (_ BitVec 49)
  (bvnot (bvlshr (bvnot (_ bv0 49)) (_ bv1 49)))
)
(define-fun max () (_ BitVec 49)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 49)) (t (_ BitVec 49))) Bool
(bvult t (bvor (bvneg s) s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 49))) (bvugt (bvmul x s) t)))
  (=> (exists ((x (_ BitVec 49))) (bvugt (bvmul x s) t)) (SC s t))
  )
 )
)
(check-sat)
