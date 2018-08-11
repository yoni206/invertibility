(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 40))
(declare-fun t () (_ BitVec 40))

(define-fun udivtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) (bvnot (_ bv0 40)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) a (bvurem a b))
)
(define-fun min () (_ BitVec 40)
  (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40)))
)
(define-fun max () (_ BitVec 40)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 40)) (t (_ BitVec 40))) Bool
(or  (= (bvlshr s (_ bv0 40)) t) (= (bvlshr s (_ bv1 40)) t) (= (bvlshr s (_ bv2 40)) t) (= (bvlshr s (_ bv3 40)) t) (= (bvlshr s (_ bv4 40)) t) (= (bvlshr s (_ bv5 40)) t) (= (bvlshr s (_ bv6 40)) t) (= (bvlshr s (_ bv7 40)) t) (= (bvlshr s (_ bv8 40)) t) (= (bvlshr s (_ bv9 40)) t) (= (bvlshr s (_ bv10 40)) t) (= (bvlshr s (_ bv11 40)) t) (= (bvlshr s (_ bv12 40)) t) (= (bvlshr s (_ bv13 40)) t) (= (bvlshr s (_ bv14 40)) t) (= (bvlshr s (_ bv15 40)) t) (= (bvlshr s (_ bv16 40)) t) (= (bvlshr s (_ bv17 40)) t) (= (bvlshr s (_ bv18 40)) t) (= (bvlshr s (_ bv19 40)) t) (= (bvlshr s (_ bv20 40)) t) (= (bvlshr s (_ bv21 40)) t) (= (bvlshr s (_ bv22 40)) t) (= (bvlshr s (_ bv23 40)) t) (= (bvlshr s (_ bv24 40)) t) (= (bvlshr s (_ bv25 40)) t) (= (bvlshr s (_ bv26 40)) t) (= (bvlshr s (_ bv27 40)) t) (= (bvlshr s (_ bv28 40)) t) (= (bvlshr s (_ bv29 40)) t) (= (bvlshr s (_ bv30 40)) t) (= (bvlshr s (_ bv31 40)) t) (= (bvlshr s (_ bv32 40)) t) (= (bvlshr s (_ bv33 40)) t) (= (bvlshr s (_ bv34 40)) t) (= (bvlshr s (_ bv35 40)) t) (= (bvlshr s (_ bv36 40)) t) (= (bvlshr s (_ bv37 40)) t) (= (bvlshr s (_ bv38 40)) t) (= (bvlshr s (_ bv39 40)) t) (= (bvlshr s (_ bv40 40)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 40))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 40))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
