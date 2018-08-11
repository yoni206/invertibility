(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 46))
(declare-fun t () (_ BitVec 46))

(define-fun udivtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) (bvnot (_ bv0 46)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) a (bvurem a b))
)
(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 46)) (t (_ BitVec 46))) Bool
(or  (= (bvashr s (_ bv0 46)) t) (= (bvashr s (_ bv1 46)) t) (= (bvashr s (_ bv2 46)) t) (= (bvashr s (_ bv3 46)) t) (= (bvashr s (_ bv4 46)) t) (= (bvashr s (_ bv5 46)) t) (= (bvashr s (_ bv6 46)) t) (= (bvashr s (_ bv7 46)) t) (= (bvashr s (_ bv8 46)) t) (= (bvashr s (_ bv9 46)) t) (= (bvashr s (_ bv10 46)) t) (= (bvashr s (_ bv11 46)) t) (= (bvashr s (_ bv12 46)) t) (= (bvashr s (_ bv13 46)) t) (= (bvashr s (_ bv14 46)) t) (= (bvashr s (_ bv15 46)) t) (= (bvashr s (_ bv16 46)) t) (= (bvashr s (_ bv17 46)) t) (= (bvashr s (_ bv18 46)) t) (= (bvashr s (_ bv19 46)) t) (= (bvashr s (_ bv20 46)) t) (= (bvashr s (_ bv21 46)) t) (= (bvashr s (_ bv22 46)) t) (= (bvashr s (_ bv23 46)) t) (= (bvashr s (_ bv24 46)) t) (= (bvashr s (_ bv25 46)) t) (= (bvashr s (_ bv26 46)) t) (= (bvashr s (_ bv27 46)) t) (= (bvashr s (_ bv28 46)) t) (= (bvashr s (_ bv29 46)) t) (= (bvashr s (_ bv30 46)) t) (= (bvashr s (_ bv31 46)) t) (= (bvashr s (_ bv32 46)) t) (= (bvashr s (_ bv33 46)) t) (= (bvashr s (_ bv34 46)) t) (= (bvashr s (_ bv35 46)) t) (= (bvashr s (_ bv36 46)) t) (= (bvashr s (_ bv37 46)) t) (= (bvashr s (_ bv38 46)) t) (= (bvashr s (_ bv39 46)) t) (= (bvashr s (_ bv40 46)) t) (= (bvashr s (_ bv41 46)) t) (= (bvashr s (_ bv42 46)) t) (= (bvashr s (_ bv43 46)) t) (= (bvashr s (_ bv44 46)) t) (= (bvashr s (_ bv45 46)) t) (= (bvashr s (_ bv46 46)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 46))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 46))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
