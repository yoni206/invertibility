(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 34))
(declare-fun t () (_ BitVec 34))

(define-fun udivtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) (bvnot (_ bv0 34)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) a (bvurem a b))
)
(define-fun min () (_ BitVec 34)
  (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34)))
)
(define-fun max () (_ BitVec 34)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 34)) (t (_ BitVec 34))) Bool
(or  (bvsge (bvshl s (_ bv0 34)) t) (bvsge (bvshl s (_ bv1 34)) t) (bvsge (bvshl s (_ bv2 34)) t) (bvsge (bvshl s (_ bv3 34)) t) (bvsge (bvshl s (_ bv4 34)) t) (bvsge (bvshl s (_ bv5 34)) t) (bvsge (bvshl s (_ bv6 34)) t) (bvsge (bvshl s (_ bv7 34)) t) (bvsge (bvshl s (_ bv8 34)) t) (bvsge (bvshl s (_ bv9 34)) t) (bvsge (bvshl s (_ bv10 34)) t) (bvsge (bvshl s (_ bv11 34)) t) (bvsge (bvshl s (_ bv12 34)) t) (bvsge (bvshl s (_ bv13 34)) t) (bvsge (bvshl s (_ bv14 34)) t) (bvsge (bvshl s (_ bv15 34)) t) (bvsge (bvshl s (_ bv16 34)) t) (bvsge (bvshl s (_ bv17 34)) t) (bvsge (bvshl s (_ bv18 34)) t) (bvsge (bvshl s (_ bv19 34)) t) (bvsge (bvshl s (_ bv20 34)) t) (bvsge (bvshl s (_ bv21 34)) t) (bvsge (bvshl s (_ bv22 34)) t) (bvsge (bvshl s (_ bv23 34)) t) (bvsge (bvshl s (_ bv24 34)) t) (bvsge (bvshl s (_ bv25 34)) t) (bvsge (bvshl s (_ bv26 34)) t) (bvsge (bvshl s (_ bv27 34)) t) (bvsge (bvshl s (_ bv28 34)) t) (bvsge (bvshl s (_ bv29 34)) t) (bvsge (bvshl s (_ bv30 34)) t) (bvsge (bvshl s (_ bv31 34)) t) (bvsge (bvshl s (_ bv32 34)) t) (bvsge (bvshl s (_ bv33 34)) t) (bvsge (bvshl s (_ bv34 34)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 34))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 34))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
