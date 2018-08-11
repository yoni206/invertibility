(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 24))
(declare-fun t () (_ BitVec 24))

(define-fun udivtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) (bvnot (_ bv0 24)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) a (bvurem a b))
)
(define-fun min () (_ BitVec 24)
  (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24)))
)
(define-fun max () (_ BitVec 24)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 24)) (t (_ BitVec 24))) Bool
(and (=> (bvslt s (_ bv0 24)) (bvsgt (bvlshr s (_ bv1 24)) t)) (=> (bvsge s (_ bv0 24)) (bvsgt s t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 24))) (bvsgt (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 24))) (bvsgt (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
