(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 41))
(declare-fun t () (_ BitVec 41))

(define-fun udivtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) (bvnot (_ bv0 41)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) a (bvurem a b))
)
(define-fun min () (_ BitVec 41)
  (bvnot (bvlshr (bvnot (_ bv0 41)) (_ bv1 41)))
)
(define-fun max () (_ BitVec 41)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 41)) (t (_ BitVec 41))) Bool
(or  (bvsge (bvshl s (_ bv0 41)) t) (bvsge (bvshl s (_ bv1 41)) t) (bvsge (bvshl s (_ bv2 41)) t) (bvsge (bvshl s (_ bv3 41)) t) (bvsge (bvshl s (_ bv4 41)) t) (bvsge (bvshl s (_ bv5 41)) t) (bvsge (bvshl s (_ bv6 41)) t) (bvsge (bvshl s (_ bv7 41)) t) (bvsge (bvshl s (_ bv8 41)) t) (bvsge (bvshl s (_ bv9 41)) t) (bvsge (bvshl s (_ bv10 41)) t) (bvsge (bvshl s (_ bv11 41)) t) (bvsge (bvshl s (_ bv12 41)) t) (bvsge (bvshl s (_ bv13 41)) t) (bvsge (bvshl s (_ bv14 41)) t) (bvsge (bvshl s (_ bv15 41)) t) (bvsge (bvshl s (_ bv16 41)) t) (bvsge (bvshl s (_ bv17 41)) t) (bvsge (bvshl s (_ bv18 41)) t) (bvsge (bvshl s (_ bv19 41)) t) (bvsge (bvshl s (_ bv20 41)) t) (bvsge (bvshl s (_ bv21 41)) t) (bvsge (bvshl s (_ bv22 41)) t) (bvsge (bvshl s (_ bv23 41)) t) (bvsge (bvshl s (_ bv24 41)) t) (bvsge (bvshl s (_ bv25 41)) t) (bvsge (bvshl s (_ bv26 41)) t) (bvsge (bvshl s (_ bv27 41)) t) (bvsge (bvshl s (_ bv28 41)) t) (bvsge (bvshl s (_ bv29 41)) t) (bvsge (bvshl s (_ bv30 41)) t) (bvsge (bvshl s (_ bv31 41)) t) (bvsge (bvshl s (_ bv32 41)) t) (bvsge (bvshl s (_ bv33 41)) t) (bvsge (bvshl s (_ bv34 41)) t) (bvsge (bvshl s (_ bv35 41)) t) (bvsge (bvshl s (_ bv36 41)) t) (bvsge (bvshl s (_ bv37 41)) t) (bvsge (bvshl s (_ bv38 41)) t) (bvsge (bvshl s (_ bv39 41)) t) (bvsge (bvshl s (_ bv40 41)) t) (bvsge (bvshl s (_ bv41 41)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 41))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 41))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
