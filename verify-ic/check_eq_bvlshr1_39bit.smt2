(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 39))
(declare-fun t () (_ BitVec 39))

(define-fun udivtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) (bvnot (_ bv0 39)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) a (bvurem a b))
)
(define-fun min () (_ BitVec 39)
  (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39)))
)
(define-fun max () (_ BitVec 39)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 39)) (t (_ BitVec 39))) Bool
(or  (= (bvlshr s (_ bv0 39)) t) (= (bvlshr s (_ bv1 39)) t) (= (bvlshr s (_ bv2 39)) t) (= (bvlshr s (_ bv3 39)) t) (= (bvlshr s (_ bv4 39)) t) (= (bvlshr s (_ bv5 39)) t) (= (bvlshr s (_ bv6 39)) t) (= (bvlshr s (_ bv7 39)) t) (= (bvlshr s (_ bv8 39)) t) (= (bvlshr s (_ bv9 39)) t) (= (bvlshr s (_ bv10 39)) t) (= (bvlshr s (_ bv11 39)) t) (= (bvlshr s (_ bv12 39)) t) (= (bvlshr s (_ bv13 39)) t) (= (bvlshr s (_ bv14 39)) t) (= (bvlshr s (_ bv15 39)) t) (= (bvlshr s (_ bv16 39)) t) (= (bvlshr s (_ bv17 39)) t) (= (bvlshr s (_ bv18 39)) t) (= (bvlshr s (_ bv19 39)) t) (= (bvlshr s (_ bv20 39)) t) (= (bvlshr s (_ bv21 39)) t) (= (bvlshr s (_ bv22 39)) t) (= (bvlshr s (_ bv23 39)) t) (= (bvlshr s (_ bv24 39)) t) (= (bvlshr s (_ bv25 39)) t) (= (bvlshr s (_ bv26 39)) t) (= (bvlshr s (_ bv27 39)) t) (= (bvlshr s (_ bv28 39)) t) (= (bvlshr s (_ bv29 39)) t) (= (bvlshr s (_ bv30 39)) t) (= (bvlshr s (_ bv31 39)) t) (= (bvlshr s (_ bv32 39)) t) (= (bvlshr s (_ bv33 39)) t) (= (bvlshr s (_ bv34 39)) t) (= (bvlshr s (_ bv35 39)) t) (= (bvlshr s (_ bv36 39)) t) (= (bvlshr s (_ bv37 39)) t) (= (bvlshr s (_ bv38 39)) t) (= (bvlshr s (_ bv39 39)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 39))) (= (bvlshr s x) t)))
  (=> (exists ((x (_ BitVec 39))) (= (bvlshr s x) t)) (SC s t))
  )
 )
)
(check-sat)
