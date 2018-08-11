(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)
(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 60)) (t (_ BitVec 60))) Bool
(bvuge (bvshl (bvnot (_ bv0 60)) s) t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 60))) (bvuge (bvshl x s) t)))
  (=> (exists ((x (_ BitVec 60))) (bvuge (bvshl x s) t)) (SC s t))
  )
 )
)
(check-sat)
