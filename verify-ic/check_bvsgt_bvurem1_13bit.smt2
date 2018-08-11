(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 13))
(declare-fun t () (_ BitVec 13))

(define-fun udivtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) (bvnot (_ bv0 13)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) a (bvurem a b))
)
(define-fun min () (_ BitVec 13)
  (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13)))
)
(define-fun max () (_ BitVec 13)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 13)) (t (_ BitVec 13))) Bool
(and (=> (bvsge s (_ bv0 13)) (bvsgt s t)) (=> (bvslt s (_ bv0 13)) (bvsgt (bvlshr (bvsub s (_ bv1 13)) (_ bv1 13)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 13))) (bvsgt (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 13))) (bvsgt (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
