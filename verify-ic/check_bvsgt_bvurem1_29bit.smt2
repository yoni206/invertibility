(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 29))
(declare-fun t () (_ BitVec 29))

(define-fun udivtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) (bvnot (_ bv0 29)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) a (bvurem a b))
)
(define-fun min () (_ BitVec 29)
  (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29)))
)
(define-fun max () (_ BitVec 29)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 29)) (t (_ BitVec 29))) Bool
(and (=> (bvsge s (_ bv0 29)) (bvsgt s t)) (=> (bvslt s (_ bv0 29)) (bvsgt (bvlshr (bvsub s (_ bv1 29)) (_ bv1 29)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 29))) (bvsgt (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 29))) (bvsgt (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
