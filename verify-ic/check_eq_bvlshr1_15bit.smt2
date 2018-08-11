(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 15))
(declare-fun t () (_ BitVec 15))

(define-fun udivtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) (bvnot (_ bv0 15)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) a (bvurem a b))
)
(define-fun min () (_ BitVec 15)
  (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15)))
)
(define-fun max () (_ BitVec 15)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 15)) (t (_ BitVec 15))) Bool
(or  (= (bvlshr s (_ bv0 15)) t) (= (bvlshr s (_ bv1 15)) t) (= (bvlshr s (_ bv2 15)) t) (= (bvlshr s (_ bv3 15)) t) (= (bvlshr s (_ bv4 15)) t) (= (bvlshr s (_ bv5 15)) t) (= (bvlshr s (_ bv6 15)) t) (= (bvlshr s (_ bv7 15)) t) (= (bvlshr s (_ bv8 15)) t) (= (bvlshr s (_ bv9 15)) t) (= (bvlshr s (_ bv10 15)) t) (= (bvlshr s (_ bv11 15)) t) (= (bvlshr s (_ bv12 15)) t) (= (bvlshr s (_ bv13 15)) t) (= (bvlshr s (_ bv14 15)) t) (= (bvlshr s (_ bv15 15)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 15))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 15))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
