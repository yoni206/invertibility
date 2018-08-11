(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 55))
(declare-fun t () (_ BitVec 55))

(define-fun udivtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) (bvnot (_ bv0 55)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) a (bvurem a b))
)
(define-fun min () (_ BitVec 55)
  (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55)))
)
(define-fun max () (_ BitVec 55)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 55)) (t (_ BitVec 55))) Bool
(and (=> (bvsge s (_ bv0 55)) (bvsge s t)) (=> (bvslt s (_ bv0 55)) (bvsge (bvlshr s (_ bv1 55)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 55))) (bvsge (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 55))) (bvsge (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
