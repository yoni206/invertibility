(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 51))
(declare-fun t () (_ BitVec 51))

(define-fun udivtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) (bvnot (_ bv0 51)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) a (bvurem a b))
)
(define-fun min () (_ BitVec 51)
  (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51)))
)
(define-fun max () (_ BitVec 51)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 51)) (t (_ BitVec 51))) Bool
(and (=> (bvsge s (_ bv0 51)) (bvsge s t)) (=> (and (bvslt s (_ bv0 51)) (bvsge t (_ bv0 51))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 51))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 51))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
