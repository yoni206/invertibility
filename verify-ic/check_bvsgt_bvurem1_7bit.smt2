(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))

(define-fun udivtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) (bvnot (_ bv0 7)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) a (bvurem a b))
)
(define-fun min () (_ BitVec 7)
  (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7)))
)
(define-fun max () (_ BitVec 7)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 7)) (t (_ BitVec 7))) Bool
(and (=> (bvsge s (_ bv0 7)) (bvsgt s t)) (=> (bvslt s (_ bv0 7)) (bvsgt (bvlshr (bvsub s (_ bv1 7)) (_ bv1 7)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 7))) (bvsgt (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 7))) (bvsgt (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
