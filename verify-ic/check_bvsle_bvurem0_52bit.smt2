(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 52))
(declare-fun t () (_ BitVec 52))

(define-fun udivtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) (bvnot (_ bv0 52)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) a (bvurem a b))
)
(define-fun min () (_ BitVec 52)
  (bvnot (bvlshr (bvnot (_ bv0 52)) (_ bv1 52)))
)
(define-fun max () (_ BitVec 52)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 52)) (t (_ BitVec 52))) Bool
(bvslt (bvnot (_ bv0 52)) (bvand (bvneg s) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 52))) (bvsle (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 52))) (bvsle (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
