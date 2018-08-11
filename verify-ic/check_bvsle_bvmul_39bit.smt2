(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 39))
(declare-fun t () (_ BitVec 39))

(define-fun udivtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) (bvnot (_ bv0 39)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) a (bvurem a b))
)
(define-fun min () (_ BitVec 39)
  (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39)))
)
(define-fun max () (_ BitVec 39)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 39)) (t (_ BitVec 39))) Bool
(not (and (= s (_ bv0 39)) (bvslt t s)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 39))) (bvsle (bvmul x s) t)))
  (=> (exists ((x (_ BitVec 39))) (bvsle (bvmul x s) t)) (SC s t))
  )
 )
)
(check-sat)
