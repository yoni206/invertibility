(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 23))
(declare-fun t () (_ BitVec 23))

(define-fun udivtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) (bvnot (_ bv0 23)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) a (bvurem a b))
)
(define-fun min () (_ BitVec 23)
  (bvnot (bvlshr (bvnot (_ bv0 23)) (_ bv1 23)))
)
(define-fun max () (_ BitVec 23)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 23)) (t (_ BitVec 23))) Bool
(or  (bvsge (bvshl s (_ bv0 23)) t) (bvsge (bvshl s (_ bv1 23)) t) (bvsge (bvshl s (_ bv2 23)) t) (bvsge (bvshl s (_ bv3 23)) t) (bvsge (bvshl s (_ bv4 23)) t) (bvsge (bvshl s (_ bv5 23)) t) (bvsge (bvshl s (_ bv6 23)) t) (bvsge (bvshl s (_ bv7 23)) t) (bvsge (bvshl s (_ bv8 23)) t) (bvsge (bvshl s (_ bv9 23)) t) (bvsge (bvshl s (_ bv10 23)) t) (bvsge (bvshl s (_ bv11 23)) t) (bvsge (bvshl s (_ bv12 23)) t) (bvsge (bvshl s (_ bv13 23)) t) (bvsge (bvshl s (_ bv14 23)) t) (bvsge (bvshl s (_ bv15 23)) t) (bvsge (bvshl s (_ bv16 23)) t) (bvsge (bvshl s (_ bv17 23)) t) (bvsge (bvshl s (_ bv18 23)) t) (bvsge (bvshl s (_ bv19 23)) t) (bvsge (bvshl s (_ bv20 23)) t) (bvsge (bvshl s (_ bv21 23)) t) (bvsge (bvshl s (_ bv22 23)) t) (bvsge (bvshl s (_ bv23 23)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 23))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 23))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
