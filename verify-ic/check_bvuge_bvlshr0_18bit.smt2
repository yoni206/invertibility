(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 18))
(declare-fun t () (_ BitVec 18))

(define-fun udivtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) (bvnot (_ bv0 18)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) a (bvurem a b))
)
(define-fun min () (_ BitVec 18)
  (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18)))
)
(define-fun max () (_ BitVec 18)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 18)) (t (_ BitVec 18))) Bool
(= (bvlshr (bvshl t s) s) t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 18))) (bvuge (bvlshr x s) t)))
  (=> (exists ((x (_ BitVec 18))) (bvuge (bvlshr x s) t)) (SC s t))
  )
 )
)
(check-sat)
