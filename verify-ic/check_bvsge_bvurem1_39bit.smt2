(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 39))
(declare-fun t () (_ BitVec 39))

(define-fun udivtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) (bvnot (_ bv0 39)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) a (bvurem a b))
)
(define-fun min () (_ BitVec 39)
  (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39)))
)
(define-fun max () (_ BitVec 39)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 39)) (t (_ BitVec 39))) Bool
(and (=> (bvsge s (_ bv0 39)) (bvsge s t)) (=> (and (bvslt s (_ bv0 39)) (bvsge t (_ bv0 39))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 39))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 39))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
