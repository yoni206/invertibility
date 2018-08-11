(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 19))
(declare-fun t () (_ BitVec 19))

(define-fun udivtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) (bvnot (_ bv0 19)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) a (bvurem a b))
)
(define-fun min () (_ BitVec 19)
  (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19)))
)
(define-fun max () (_ BitVec 19)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 19)) (t (_ BitVec 19))) Bool
(and (=> (bvsge s (_ bv0 19)) (bvsge s t)) (=> (and (bvslt s (_ bv0 19)) (bvsge t (_ bv0 19))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 19))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 19))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
