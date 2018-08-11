(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 20))
(declare-fun t () (_ BitVec 20))

(define-fun udivtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) (bvnot (_ bv0 20)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) a (bvurem a b))
)
(define-fun min () (_ BitVec 20)
  (bvnot (bvlshr (bvnot (_ bv0 20)) (_ bv1 20)))
)
(define-fun max () (_ BitVec 20)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 20)) (t (_ BitVec 20))) Bool
(or  (= (bvlshr s (_ bv0 20)) t) (= (bvlshr s (_ bv1 20)) t) (= (bvlshr s (_ bv2 20)) t) (= (bvlshr s (_ bv3 20)) t) (= (bvlshr s (_ bv4 20)) t) (= (bvlshr s (_ bv5 20)) t) (= (bvlshr s (_ bv6 20)) t) (= (bvlshr s (_ bv7 20)) t) (= (bvlshr s (_ bv8 20)) t) (= (bvlshr s (_ bv9 20)) t) (= (bvlshr s (_ bv10 20)) t) (= (bvlshr s (_ bv11 20)) t) (= (bvlshr s (_ bv12 20)) t) (= (bvlshr s (_ bv13 20)) t) (= (bvlshr s (_ bv14 20)) t) (= (bvlshr s (_ bv15 20)) t) (= (bvlshr s (_ bv16 20)) t) (= (bvlshr s (_ bv17 20)) t) (= (bvlshr s (_ bv18 20)) t) (= (bvlshr s (_ bv19 20)) t) (= (bvlshr s (_ bv20 20)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 20))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 20))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
