(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 44))
(declare-fun t () (_ BitVec 44))

(define-fun udivtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) (bvnot (_ bv0 44)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) a (bvurem a b))
)
(define-fun min () (_ BitVec 44)
  (bvnot (bvlshr (bvnot (_ bv0 44)) (_ bv1 44)))
)
(define-fun max () (_ BitVec 44)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 44)) (t (_ BitVec 44))) Bool
(or  (bvsge (bvshl s (_ bv0 44)) t) (bvsge (bvshl s (_ bv1 44)) t) (bvsge (bvshl s (_ bv2 44)) t) (bvsge (bvshl s (_ bv3 44)) t) (bvsge (bvshl s (_ bv4 44)) t) (bvsge (bvshl s (_ bv5 44)) t) (bvsge (bvshl s (_ bv6 44)) t) (bvsge (bvshl s (_ bv7 44)) t) (bvsge (bvshl s (_ bv8 44)) t) (bvsge (bvshl s (_ bv9 44)) t) (bvsge (bvshl s (_ bv10 44)) t) (bvsge (bvshl s (_ bv11 44)) t) (bvsge (bvshl s (_ bv12 44)) t) (bvsge (bvshl s (_ bv13 44)) t) (bvsge (bvshl s (_ bv14 44)) t) (bvsge (bvshl s (_ bv15 44)) t) (bvsge (bvshl s (_ bv16 44)) t) (bvsge (bvshl s (_ bv17 44)) t) (bvsge (bvshl s (_ bv18 44)) t) (bvsge (bvshl s (_ bv19 44)) t) (bvsge (bvshl s (_ bv20 44)) t) (bvsge (bvshl s (_ bv21 44)) t) (bvsge (bvshl s (_ bv22 44)) t) (bvsge (bvshl s (_ bv23 44)) t) (bvsge (bvshl s (_ bv24 44)) t) (bvsge (bvshl s (_ bv25 44)) t) (bvsge (bvshl s (_ bv26 44)) t) (bvsge (bvshl s (_ bv27 44)) t) (bvsge (bvshl s (_ bv28 44)) t) (bvsge (bvshl s (_ bv29 44)) t) (bvsge (bvshl s (_ bv30 44)) t) (bvsge (bvshl s (_ bv31 44)) t) (bvsge (bvshl s (_ bv32 44)) t) (bvsge (bvshl s (_ bv33 44)) t) (bvsge (bvshl s (_ bv34 44)) t) (bvsge (bvshl s (_ bv35 44)) t) (bvsge (bvshl s (_ bv36 44)) t) (bvsge (bvshl s (_ bv37 44)) t) (bvsge (bvshl s (_ bv38 44)) t) (bvsge (bvshl s (_ bv39 44)) t) (bvsge (bvshl s (_ bv40 44)) t) (bvsge (bvshl s (_ bv41 44)) t) (bvsge (bvshl s (_ bv42 44)) t) (bvsge (bvshl s (_ bv43 44)) t) (bvsge (bvshl s (_ bv44 44)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 44))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 44))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
