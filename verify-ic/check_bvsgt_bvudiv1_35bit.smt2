(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)
(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 35)) (t (_ BitVec 35))) Bool
(and (=> (bvsge s (_ bv0 35)) (bvsgt s t)) (=> (bvslt s (_ bv0 35)) (bvsgt (bvlshr s (_ bv1 35)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (bvsgt (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 35))) (bvsgt (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
