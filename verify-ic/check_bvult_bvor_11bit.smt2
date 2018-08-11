(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun t () (_ BitVec 11))

(define-fun udivtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) (bvnot (_ bv0 11)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) a (bvurem a b))
)
(define-fun min () (_ BitVec 11)
  (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11)))
)
(define-fun max () (_ BitVec 11)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 11)) (t (_ BitVec 11))) Bool
(bvult s t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 11))) (bvult (bvor x s) t)))
  (=> (exists ((x (_ BitVec 11))) (bvult (bvor x s) t)) (SC s t))
  )
 )
)
(check-sat)
