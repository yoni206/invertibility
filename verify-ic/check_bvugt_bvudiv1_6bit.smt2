(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))

(define-fun udivtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) (bvnot (_ bv0 6)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) a (bvurem a b))
)
(define-fun min () (_ BitVec 6)
  (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6)))
)
(define-fun max () (_ BitVec 6)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 6)) (t (_ BitVec 6))) Bool
(bvult t (bvnot (_ bv0 6)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 6))) (bvugt (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 6))) (bvugt (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
