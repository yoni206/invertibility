(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 58))
(declare-fun t () (_ BitVec 58))

(define-fun udivtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) (bvnot (_ bv0 58)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) a (bvurem a b))
)
(define-fun min () (_ BitVec 58)
  (bvnot (bvlshr (bvnot (_ bv0 58)) (_ bv1 58)))
)
(define-fun max () (_ BitVec 58)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 58)) (t (_ BitVec 58))) Bool
(or (bvsgt (udivtotal (bvnot (_ bv0 58)) s) t) (bvsgt (udivtotal max s) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 58))) (bvsgt (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 58))) (bvsgt (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
