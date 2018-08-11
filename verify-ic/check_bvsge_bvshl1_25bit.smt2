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
(or  (bvsge (bvshl s (_ bv0 25)) t) (bvsge (bvshl s (_ bv1 25)) t) (bvsge (bvshl s (_ bv2 25)) t) (bvsge (bvshl s (_ bv3 25)) t) (bvsge (bvshl s (_ bv4 25)) t) (bvsge (bvshl s (_ bv5 25)) t) (bvsge (bvshl s (_ bv6 25)) t) (bvsge (bvshl s (_ bv7 25)) t) (bvsge (bvshl s (_ bv8 25)) t) (bvsge (bvshl s (_ bv9 25)) t) (bvsge (bvshl s (_ bv10 25)) t) (bvsge (bvshl s (_ bv11 25)) t) (bvsge (bvshl s (_ bv12 25)) t) (bvsge (bvshl s (_ bv13 25)) t) (bvsge (bvshl s (_ bv14 25)) t) (bvsge (bvshl s (_ bv15 25)) t) (bvsge (bvshl s (_ bv16 25)) t) (bvsge (bvshl s (_ bv17 25)) t) (bvsge (bvshl s (_ bv18 25)) t) (bvsge (bvshl s (_ bv19 25)) t) (bvsge (bvshl s (_ bv20 25)) t) (bvsge (bvshl s (_ bv21 25)) t) (bvsge (bvshl s (_ bv22 25)) t) (bvsge (bvshl s (_ bv23 25)) t) (bvsge (bvshl s (_ bv24 25)) t) (bvsge (bvshl s (_ bv25 25)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 25))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 25))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
