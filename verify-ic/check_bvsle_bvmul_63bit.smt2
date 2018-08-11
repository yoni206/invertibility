(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)
(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 63)) (t (_ BitVec 63))) Bool
(not (and (= s (_ bv0 63)) (bvslt t s)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 63))) (bvsle (bvmul x s) t)))
  (=> (exists ((x (_ BitVec 63))) (bvsle (bvmul x s) t)) (SC s t))
  )
 )
)
(check-sat)
