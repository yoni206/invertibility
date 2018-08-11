(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 33))
(declare-fun t () (_ BitVec 33))

(define-fun udivtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) (bvnot (_ bv0 33)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) a (bvurem a b))
)
(define-fun min () (_ BitVec 33)
  (bvnot (bvlshr (bvnot (_ bv0 33)) (_ bv1 33)))
)
(define-fun max () (_ BitVec 33)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 33)) (t (_ BitVec 33))) Bool
(= (bvand (udivtotal (bvmul s t) t) s) s)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 33))) (bvuge (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 33))) (bvuge (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
