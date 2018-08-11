(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)
(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 60)) (t (_ BitVec 60))) Bool
(and (=> (bvsge s (_ bv0 60)) (bvsge s t)) (=> (bvslt s (_ bv0 60)) (bvsge (bvlshr s (_ bv1 60)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 60))) (bvsge (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 60))) (bvsge (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
