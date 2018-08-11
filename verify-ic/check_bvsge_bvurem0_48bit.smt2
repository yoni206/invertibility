(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 48))
(declare-fun t () (_ BitVec 48))

(define-fun udivtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) (bvnot (_ bv0 48)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) a (bvurem a b))
)
(define-fun min () (_ BitVec 48)
  (bvnot (bvlshr (bvnot (_ bv0 48)) (_ bv1 48)))
)
(define-fun max () (_ BitVec 48)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 48)) (t (_ BitVec 48))) Bool
(or (bvslt t s) (bvsge (_ bv0 48) s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 48))) (bvsge (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 48))) (bvsge (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
