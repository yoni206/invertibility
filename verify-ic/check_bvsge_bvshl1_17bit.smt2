(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)
(define-fun min () (_ BitVec 17)
  (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17)))
)
(define-fun max () (_ BitVec 17)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 17)) (t (_ BitVec 17))) Bool
(or  (bvsge (bvshl s (_ bv0 17)) t) (bvsge (bvshl s (_ bv1 17)) t) (bvsge (bvshl s (_ bv2 17)) t) (bvsge (bvshl s (_ bv3 17)) t) (bvsge (bvshl s (_ bv4 17)) t) (bvsge (bvshl s (_ bv5 17)) t) (bvsge (bvshl s (_ bv6 17)) t) (bvsge (bvshl s (_ bv7 17)) t) (bvsge (bvshl s (_ bv8 17)) t) (bvsge (bvshl s (_ bv9 17)) t) (bvsge (bvshl s (_ bv10 17)) t) (bvsge (bvshl s (_ bv11 17)) t) (bvsge (bvshl s (_ bv12 17)) t) (bvsge (bvshl s (_ bv13 17)) t) (bvsge (bvshl s (_ bv14 17)) t) (bvsge (bvshl s (_ bv15 17)) t) (bvsge (bvshl s (_ bv16 17)) t) (bvsge (bvshl s (_ bv17 17)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 17))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 17))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
