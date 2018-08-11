(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 51))
(declare-fun t () (_ BitVec 51))

(define-fun udivtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) (bvnot (_ bv0 51)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) a (bvurem a b))
)
(define-fun min () (_ BitVec 51)
  (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51)))
)
(define-fun max () (_ BitVec 51)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 51)) (t (_ BitVec 51))) Bool
(or  (= (bvlshr s (_ bv0 51)) t) (= (bvlshr s (_ bv1 51)) t) (= (bvlshr s (_ bv2 51)) t) (= (bvlshr s (_ bv3 51)) t) (= (bvlshr s (_ bv4 51)) t) (= (bvlshr s (_ bv5 51)) t) (= (bvlshr s (_ bv6 51)) t) (= (bvlshr s (_ bv7 51)) t) (= (bvlshr s (_ bv8 51)) t) (= (bvlshr s (_ bv9 51)) t) (= (bvlshr s (_ bv10 51)) t) (= (bvlshr s (_ bv11 51)) t) (= (bvlshr s (_ bv12 51)) t) (= (bvlshr s (_ bv13 51)) t) (= (bvlshr s (_ bv14 51)) t) (= (bvlshr s (_ bv15 51)) t) (= (bvlshr s (_ bv16 51)) t) (= (bvlshr s (_ bv17 51)) t) (= (bvlshr s (_ bv18 51)) t) (= (bvlshr s (_ bv19 51)) t) (= (bvlshr s (_ bv20 51)) t) (= (bvlshr s (_ bv21 51)) t) (= (bvlshr s (_ bv22 51)) t) (= (bvlshr s (_ bv23 51)) t) (= (bvlshr s (_ bv24 51)) t) (= (bvlshr s (_ bv25 51)) t) (= (bvlshr s (_ bv26 51)) t) (= (bvlshr s (_ bv27 51)) t) (= (bvlshr s (_ bv28 51)) t) (= (bvlshr s (_ bv29 51)) t) (= (bvlshr s (_ bv30 51)) t) (= (bvlshr s (_ bv31 51)) t) (= (bvlshr s (_ bv32 51)) t) (= (bvlshr s (_ bv33 51)) t) (= (bvlshr s (_ bv34 51)) t) (= (bvlshr s (_ bv35 51)) t) (= (bvlshr s (_ bv36 51)) t) (= (bvlshr s (_ bv37 51)) t) (= (bvlshr s (_ bv38 51)) t) (= (bvlshr s (_ bv39 51)) t) (= (bvlshr s (_ bv40 51)) t) (= (bvlshr s (_ bv41 51)) t) (= (bvlshr s (_ bv42 51)) t) (= (bvlshr s (_ bv43 51)) t) (= (bvlshr s (_ bv44 51)) t) (= (bvlshr s (_ bv45 51)) t) (= (bvlshr s (_ bv46 51)) t) (= (bvlshr s (_ bv47 51)) t) (= (bvlshr s (_ bv48 51)) t) (= (bvlshr s (_ bv49 51)) t) (= (bvlshr s (_ bv50 51)) t) (= (bvlshr s (_ bv51 51)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 51))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 51))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
