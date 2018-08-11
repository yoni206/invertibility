(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))

(define-fun udivtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) (bvnot (_ bv0 32)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) a (bvurem a b))
)
(define-fun min () (_ BitVec 32)
  (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32)))
)
(define-fun max () (_ BitVec 32)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 32)) (t (_ BitVec 32))) Bool
(bvslt (bvand (bvnot (bvneg t)) s) t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 32))) (bvslt (bvand x s) t)))
  (=> (exists ((x (_ BitVec 32))) (bvslt (bvand x s) t)) (SC s t))
  )
 )
)
(check-sat)
