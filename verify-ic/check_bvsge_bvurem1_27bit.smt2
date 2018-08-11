(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun t () (_ BitVec 27))

(define-fun udivtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) (bvnot (_ bv0 27)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) a (bvurem a b))
)
(define-fun min () (_ BitVec 27)
  (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27)))
)
(define-fun max () (_ BitVec 27)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 27)) (t (_ BitVec 27))) Bool
(and (=> (bvsge s (_ bv0 27)) (bvsge s t)) (=> (and (bvslt s (_ bv0 27)) (bvsge t (_ bv0 27))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 27))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 27))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
