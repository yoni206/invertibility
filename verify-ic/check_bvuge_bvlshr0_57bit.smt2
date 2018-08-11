(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun t () (_ BitVec 57))

(define-fun udivtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) (bvnot (_ bv0 57)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) a (bvurem a b))
)
(define-fun min () (_ BitVec 57)
  (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57)))
)
(define-fun max () (_ BitVec 57)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 57)) (t (_ BitVec 57))) Bool
(= (bvlshr (bvshl t s) s) t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 57))) (bvuge (bvlshr x s) t)))
  (=> (exists ((x (_ BitVec 57))) (bvuge (bvlshr x s) t)) (SC s t))
  )
 )
)
(check-sat)
