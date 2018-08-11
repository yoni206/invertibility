(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 14))
(declare-fun t () (_ BitVec 14))

(define-fun udivtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) (bvnot (_ bv0 14)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) a (bvurem a b))
)
(define-fun min () (_ BitVec 14)
  (bvnot (bvlshr (bvnot (_ bv0 14)) (_ bv1 14)))
)
(define-fun max () (_ BitVec 14)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 14)) (t (_ BitVec 14))) Bool
(or  (= (bvlshr s (_ bv0 14)) t) (= (bvlshr s (_ bv1 14)) t) (= (bvlshr s (_ bv2 14)) t) (= (bvlshr s (_ bv3 14)) t) (= (bvlshr s (_ bv4 14)) t) (= (bvlshr s (_ bv5 14)) t) (= (bvlshr s (_ bv6 14)) t) (= (bvlshr s (_ bv7 14)) t) (= (bvlshr s (_ bv8 14)) t) (= (bvlshr s (_ bv9 14)) t) (= (bvlshr s (_ bv10 14)) t) (= (bvlshr s (_ bv11 14)) t) (= (bvlshr s (_ bv12 14)) t) (= (bvlshr s (_ bv13 14)) t) (= (bvlshr s (_ bv14 14)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 14))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 14))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
