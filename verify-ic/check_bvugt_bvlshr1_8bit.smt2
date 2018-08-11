(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))

(define-fun udivtotal ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 8)
  (ite (= b (_ bv0 8)) (bvnot (_ bv0 8)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 8)
  (ite (= b (_ bv0 8)) a (bvurem a b))
)
(define-fun min () (_ BitVec 8)
  (bvnot (bvlshr (bvnot (_ bv0 8)) (_ bv1 8)))
)
(define-fun max () (_ BitVec 8)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 8)) (t (_ BitVec 8))) Bool
(bvult t s)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 8))) (bvugt (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 8))) (bvugt (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
