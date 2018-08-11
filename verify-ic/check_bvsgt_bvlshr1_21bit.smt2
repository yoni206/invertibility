(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 21))
(declare-fun t () (_ BitVec 21))

(define-fun udivtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) (bvnot (_ bv0 21)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) a (bvurem a b))
)
(define-fun min () (_ BitVec 21)
  (bvnot (bvlshr (bvnot (_ bv0 21)) (_ bv1 21)))
)
(define-fun max () (_ BitVec 21)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 21)) (t (_ BitVec 21))) Bool
(and (=> (bvslt s (_ bv0 21)) (bvsgt (bvlshr s (_ bv1 21)) t)) (=> (bvsge s (_ bv0 21)) (bvsgt s t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 21))) (bvsgt (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 21))) (bvsgt (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
