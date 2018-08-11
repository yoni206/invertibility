(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 52))
(declare-fun t () (_ BitVec 52))

(define-fun udivtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) (bvnot (_ bv0 52)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) a (bvurem a b))
)
(define-fun min () (_ BitVec 52)
  (bvnot (bvlshr (bvnot (_ bv0 52)) (_ bv1 52)))
)
(define-fun max () (_ BitVec 52)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 52)) (t (_ BitVec 52))) Bool
(or  (= (bvlshr s (_ bv0 52)) t) (= (bvlshr s (_ bv1 52)) t) (= (bvlshr s (_ bv2 52)) t) (= (bvlshr s (_ bv3 52)) t) (= (bvlshr s (_ bv4 52)) t) (= (bvlshr s (_ bv5 52)) t) (= (bvlshr s (_ bv6 52)) t) (= (bvlshr s (_ bv7 52)) t) (= (bvlshr s (_ bv8 52)) t) (= (bvlshr s (_ bv9 52)) t) (= (bvlshr s (_ bv10 52)) t) (= (bvlshr s (_ bv11 52)) t) (= (bvlshr s (_ bv12 52)) t) (= (bvlshr s (_ bv13 52)) t) (= (bvlshr s (_ bv14 52)) t) (= (bvlshr s (_ bv15 52)) t) (= (bvlshr s (_ bv16 52)) t) (= (bvlshr s (_ bv17 52)) t) (= (bvlshr s (_ bv18 52)) t) (= (bvlshr s (_ bv19 52)) t) (= (bvlshr s (_ bv20 52)) t) (= (bvlshr s (_ bv21 52)) t) (= (bvlshr s (_ bv22 52)) t) (= (bvlshr s (_ bv23 52)) t) (= (bvlshr s (_ bv24 52)) t) (= (bvlshr s (_ bv25 52)) t) (= (bvlshr s (_ bv26 52)) t) (= (bvlshr s (_ bv27 52)) t) (= (bvlshr s (_ bv28 52)) t) (= (bvlshr s (_ bv29 52)) t) (= (bvlshr s (_ bv30 52)) t) (= (bvlshr s (_ bv31 52)) t) (= (bvlshr s (_ bv32 52)) t) (= (bvlshr s (_ bv33 52)) t) (= (bvlshr s (_ bv34 52)) t) (= (bvlshr s (_ bv35 52)) t) (= (bvlshr s (_ bv36 52)) t) (= (bvlshr s (_ bv37 52)) t) (= (bvlshr s (_ bv38 52)) t) (= (bvlshr s (_ bv39 52)) t) (= (bvlshr s (_ bv40 52)) t) (= (bvlshr s (_ bv41 52)) t) (= (bvlshr s (_ bv42 52)) t) (= (bvlshr s (_ bv43 52)) t) (= (bvlshr s (_ bv44 52)) t) (= (bvlshr s (_ bv45 52)) t) (= (bvlshr s (_ bv46 52)) t) (= (bvlshr s (_ bv47 52)) t) (= (bvlshr s (_ bv48 52)) t) (= (bvlshr s (_ bv49 52)) t) (= (bvlshr s (_ bv50 52)) t) (= (bvlshr s (_ bv51 52)) t) (= (bvlshr s (_ bv52 52)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 52))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 52))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
