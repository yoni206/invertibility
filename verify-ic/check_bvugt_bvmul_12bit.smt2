(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 12))
(declare-fun t () (_ BitVec 12))

(define-fun udivtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) (bvnot (_ bv0 12)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) a (bvurem a b))
)
(define-fun min () (_ BitVec 12)
  (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12)))
)
(define-fun max () (_ BitVec 12)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 12)) (t (_ BitVec 12))) Bool
(bvult t (bvor (bvneg s) s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 12))) (bvugt (bvmul x s) t)))
  (=> (exists ((x (_ BitVec 12))) (bvugt (bvmul x s) t)) (SC s t))
  )
 )
)
(check-sat)
