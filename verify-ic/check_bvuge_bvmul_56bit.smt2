(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 56))
(declare-fun t () (_ BitVec 56))

(define-fun udivtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) (bvnot (_ bv0 56)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) a (bvurem a b))
)
(define-fun min () (_ BitVec 56)
  (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56)))
)
(define-fun max () (_ BitVec 56)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 56)) (t (_ BitVec 56))) Bool
(not (bvult (bvor (bvneg s) s) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 56))) (bvuge (bvmul x s) t)))
  (=> (exists ((x (_ BitVec 56))) (bvuge (bvmul x s) t)) (SC s t))
  )
 )
)
(check-sat)
