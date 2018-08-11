(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)
(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 63)) (t (_ BitVec 63))) Bool
(and (=> (bvsge s (_ bv0 63)) (bvsge s t)) (=> (and (bvslt s (_ bv0 63)) (bvsge t (_ bv0 63))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 63))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 63))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
