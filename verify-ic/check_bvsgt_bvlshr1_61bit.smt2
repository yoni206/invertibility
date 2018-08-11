(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 61))
(declare-fun t () (_ BitVec 61))

(define-fun udivtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) (bvnot (_ bv0 61)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) a (bvurem a b))
)
(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 61)) (t (_ BitVec 61))) Bool
(and (=> (bvslt s (_ bv0 61)) (bvsgt (bvlshr s (_ bv1 61)) t)) (=> (bvsge s (_ bv0 61)) (bvsgt s t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 61))) (bvsgt (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 61))) (bvsgt (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
