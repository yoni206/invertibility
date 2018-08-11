(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 10))
(declare-fun t () (_ BitVec 10))

(define-fun udivtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) (bvnot (_ bv0 10)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) a (bvurem a b))
)
(define-fun min () (_ BitVec 10)
  (bvnot (bvlshr (bvnot (_ bv0 10)) (_ bv1 10)))
)
(define-fun max () (_ BitVec 10)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 10)) (t (_ BitVec 10))) Bool
(or (= (udivtotal (bvmul s t) s) t) (=> (bvsle t (_ bv0 10)) (bvslt (udivtotal min s) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 10))) (bvsle (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 10))) (bvsle (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
