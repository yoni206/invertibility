(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))

(define-fun udivtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) (bvnot (_ bv0 32)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) a (bvurem a b))
)
(define-fun min () (_ BitVec 32)
  (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32)))
)
(define-fun max () (_ BitVec 32)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 32)) (t (_ BitVec 32))) Bool
(or  (= (bvlshr s (_ bv0 32)) t) (= (bvlshr s (_ bv1 32)) t) (= (bvlshr s (_ bv2 32)) t) (= (bvlshr s (_ bv3 32)) t) (= (bvlshr s (_ bv4 32)) t) (= (bvlshr s (_ bv5 32)) t) (= (bvlshr s (_ bv6 32)) t) (= (bvlshr s (_ bv7 32)) t) (= (bvlshr s (_ bv8 32)) t) (= (bvlshr s (_ bv9 32)) t) (= (bvlshr s (_ bv10 32)) t) (= (bvlshr s (_ bv11 32)) t) (= (bvlshr s (_ bv12 32)) t) (= (bvlshr s (_ bv13 32)) t) (= (bvlshr s (_ bv14 32)) t) (= (bvlshr s (_ bv15 32)) t) (= (bvlshr s (_ bv16 32)) t) (= (bvlshr s (_ bv17 32)) t) (= (bvlshr s (_ bv18 32)) t) (= (bvlshr s (_ bv19 32)) t) (= (bvlshr s (_ bv20 32)) t) (= (bvlshr s (_ bv21 32)) t) (= (bvlshr s (_ bv22 32)) t) (= (bvlshr s (_ bv23 32)) t) (= (bvlshr s (_ bv24 32)) t) (= (bvlshr s (_ bv25 32)) t) (= (bvlshr s (_ bv26 32)) t) (= (bvlshr s (_ bv27 32)) t) (= (bvlshr s (_ bv28 32)) t) (= (bvlshr s (_ bv29 32)) t) (= (bvlshr s (_ bv30 32)) t) (= (bvlshr s (_ bv31 32)) t) (= (bvlshr s (_ bv32 32)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 32))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 32))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
