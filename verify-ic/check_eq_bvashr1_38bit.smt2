(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 38))
(declare-fun t () (_ BitVec 38))

(define-fun udivtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) (bvnot (_ bv0 38)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) a (bvurem a b))
)
(define-fun min () (_ BitVec 38)
  (bvnot (bvlshr (bvnot (_ bv0 38)) (_ bv1 38)))
)
(define-fun max () (_ BitVec 38)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 38)) (t (_ BitVec 38))) Bool
(or  (= (bvashr s (_ bv0 38)) t) (= (bvashr s (_ bv1 38)) t) (= (bvashr s (_ bv2 38)) t) (= (bvashr s (_ bv3 38)) t) (= (bvashr s (_ bv4 38)) t) (= (bvashr s (_ bv5 38)) t) (= (bvashr s (_ bv6 38)) t) (= (bvashr s (_ bv7 38)) t) (= (bvashr s (_ bv8 38)) t) (= (bvashr s (_ bv9 38)) t) (= (bvashr s (_ bv10 38)) t) (= (bvashr s (_ bv11 38)) t) (= (bvashr s (_ bv12 38)) t) (= (bvashr s (_ bv13 38)) t) (= (bvashr s (_ bv14 38)) t) (= (bvashr s (_ bv15 38)) t) (= (bvashr s (_ bv16 38)) t) (= (bvashr s (_ bv17 38)) t) (= (bvashr s (_ bv18 38)) t) (= (bvashr s (_ bv19 38)) t) (= (bvashr s (_ bv20 38)) t) (= (bvashr s (_ bv21 38)) t) (= (bvashr s (_ bv22 38)) t) (= (bvashr s (_ bv23 38)) t) (= (bvashr s (_ bv24 38)) t) (= (bvashr s (_ bv25 38)) t) (= (bvashr s (_ bv26 38)) t) (= (bvashr s (_ bv27 38)) t) (= (bvashr s (_ bv28 38)) t) (= (bvashr s (_ bv29 38)) t) (= (bvashr s (_ bv30 38)) t) (= (bvashr s (_ bv31 38)) t) (= (bvashr s (_ bv32 38)) t) (= (bvashr s (_ bv33 38)) t) (= (bvashr s (_ bv34 38)) t) (= (bvashr s (_ bv35 38)) t) (= (bvashr s (_ bv36 38)) t) (= (bvashr s (_ bv37 38)) t) (= (bvashr s (_ bv38 38)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 38))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 38))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
