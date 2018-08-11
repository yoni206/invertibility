(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 36))
(declare-fun t () (_ BitVec 36))

(define-fun udivtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) (bvnot (_ bv0 36)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) a (bvurem a b))
)
(define-fun min () (_ BitVec 36)
  (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36)))
)
(define-fun max () (_ BitVec 36)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 36)) (t (_ BitVec 36))) Bool
(bvslt t (bvor s max))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 36))) (bvsgt (bvor x s) t)))
  (=> (exists ((x (_ BitVec 36))) (bvsgt (bvor x s) t)) (SC s t))
  )
 )
)
(check-sat)
