(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun t () (_ BitVec 37))

(define-fun udivtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) (bvnot (_ bv0 37)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) a (bvurem a b))
)
(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 37)) (t (_ BitVec 37))) Bool
(or (= (udivtotal (bvmul s t) s) t) (=> (bvsle t (_ bv0 37)) (bvslt (udivtotal min s) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 37))) (bvsle (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 37))) (bvsle (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
