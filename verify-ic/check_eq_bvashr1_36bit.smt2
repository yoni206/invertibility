(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 36))
(declare-fun t () (_ BitVec 36))

(define-fun udivtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) (bvnot (_ bv0 36)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) a (bvurem a b))
)
(define-fun min () (_ BitVec 36)
  (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36)))
)
(define-fun max () (_ BitVec 36)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 36)) (t (_ BitVec 36))) Bool
(or  (= (bvashr s (_ bv0 36)) t) (= (bvashr s (_ bv1 36)) t) (= (bvashr s (_ bv2 36)) t) (= (bvashr s (_ bv3 36)) t) (= (bvashr s (_ bv4 36)) t) (= (bvashr s (_ bv5 36)) t) (= (bvashr s (_ bv6 36)) t) (= (bvashr s (_ bv7 36)) t) (= (bvashr s (_ bv8 36)) t) (= (bvashr s (_ bv9 36)) t) (= (bvashr s (_ bv10 36)) t) (= (bvashr s (_ bv11 36)) t) (= (bvashr s (_ bv12 36)) t) (= (bvashr s (_ bv13 36)) t) (= (bvashr s (_ bv14 36)) t) (= (bvashr s (_ bv15 36)) t) (= (bvashr s (_ bv16 36)) t) (= (bvashr s (_ bv17 36)) t) (= (bvashr s (_ bv18 36)) t) (= (bvashr s (_ bv19 36)) t) (= (bvashr s (_ bv20 36)) t) (= (bvashr s (_ bv21 36)) t) (= (bvashr s (_ bv22 36)) t) (= (bvashr s (_ bv23 36)) t) (= (bvashr s (_ bv24 36)) t) (= (bvashr s (_ bv25 36)) t) (= (bvashr s (_ bv26 36)) t) (= (bvashr s (_ bv27 36)) t) (= (bvashr s (_ bv28 36)) t) (= (bvashr s (_ bv29 36)) t) (= (bvashr s (_ bv30 36)) t) (= (bvashr s (_ bv31 36)) t) (= (bvashr s (_ bv32 36)) t) (= (bvashr s (_ bv33 36)) t) (= (bvashr s (_ bv34 36)) t) (= (bvashr s (_ bv35 36)) t) (= (bvashr s (_ bv36 36)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 36))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 36))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
