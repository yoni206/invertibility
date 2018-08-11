(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun t () (_ BitVec 37))

(define-fun udivtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) (bvnot (_ bv0 37)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) a (bvurem a b))
)
(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 37)) (t (_ BitVec 37))) Bool
(or  (= (bvlshr s (_ bv0 37)) t) (= (bvlshr s (_ bv1 37)) t) (= (bvlshr s (_ bv2 37)) t) (= (bvlshr s (_ bv3 37)) t) (= (bvlshr s (_ bv4 37)) t) (= (bvlshr s (_ bv5 37)) t) (= (bvlshr s (_ bv6 37)) t) (= (bvlshr s (_ bv7 37)) t) (= (bvlshr s (_ bv8 37)) t) (= (bvlshr s (_ bv9 37)) t) (= (bvlshr s (_ bv10 37)) t) (= (bvlshr s (_ bv11 37)) t) (= (bvlshr s (_ bv12 37)) t) (= (bvlshr s (_ bv13 37)) t) (= (bvlshr s (_ bv14 37)) t) (= (bvlshr s (_ bv15 37)) t) (= (bvlshr s (_ bv16 37)) t) (= (bvlshr s (_ bv17 37)) t) (= (bvlshr s (_ bv18 37)) t) (= (bvlshr s (_ bv19 37)) t) (= (bvlshr s (_ bv20 37)) t) (= (bvlshr s (_ bv21 37)) t) (= (bvlshr s (_ bv22 37)) t) (= (bvlshr s (_ bv23 37)) t) (= (bvlshr s (_ bv24 37)) t) (= (bvlshr s (_ bv25 37)) t) (= (bvlshr s (_ bv26 37)) t) (= (bvlshr s (_ bv27 37)) t) (= (bvlshr s (_ bv28 37)) t) (= (bvlshr s (_ bv29 37)) t) (= (bvlshr s (_ bv30 37)) t) (= (bvlshr s (_ bv31 37)) t) (= (bvlshr s (_ bv32 37)) t) (= (bvlshr s (_ bv33 37)) t) (= (bvlshr s (_ bv34 37)) t) (= (bvlshr s (_ bv35 37)) t) (= (bvlshr s (_ bv36 37)) t) (= (bvlshr s (_ bv37 37)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 37))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 37))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
