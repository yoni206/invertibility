(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 25))
(declare-fun t () (_ BitVec 25))

(define-fun udivtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) (bvnot (_ bv0 25)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) a (bvurem a b))
)
(define-fun min () (_ BitVec 25)
  (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25)))
)
(define-fun max () (_ BitVec 25)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 25)) (t (_ BitVec 25))) Bool
(or (= (udivtotal (bvmul s t) s) t) (=> (bvsle t (_ bv0 25)) (bvslt (udivtotal min s) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 25))) (bvsle (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 25))) (bvsle (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
