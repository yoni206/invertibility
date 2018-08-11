(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 54))
(declare-fun t () (_ BitVec 54))

(define-fun udivtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) (bvnot (_ bv0 54)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) a (bvurem a b))
)
(define-fun min () (_ BitVec 54)
  (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54)))
)
(define-fun max () (_ BitVec 54)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 54)) (t (_ BitVec 54))) Bool
(= (bvand (udivtotal (bvmul s t) t) s) s)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 54))) (bvuge (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 54))) (bvuge (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
