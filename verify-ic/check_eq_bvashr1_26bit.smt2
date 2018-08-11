(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 26))
(declare-fun t () (_ BitVec 26))

(define-fun udivtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) (bvnot (_ bv0 26)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) a (bvurem a b))
)
(define-fun min () (_ BitVec 26)
  (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26)))
)
(define-fun max () (_ BitVec 26)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 26)) (t (_ BitVec 26))) Bool
(or  (= (bvashr s (_ bv0 26)) t) (= (bvashr s (_ bv1 26)) t) (= (bvashr s (_ bv2 26)) t) (= (bvashr s (_ bv3 26)) t) (= (bvashr s (_ bv4 26)) t) (= (bvashr s (_ bv5 26)) t) (= (bvashr s (_ bv6 26)) t) (= (bvashr s (_ bv7 26)) t) (= (bvashr s (_ bv8 26)) t) (= (bvashr s (_ bv9 26)) t) (= (bvashr s (_ bv10 26)) t) (= (bvashr s (_ bv11 26)) t) (= (bvashr s (_ bv12 26)) t) (= (bvashr s (_ bv13 26)) t) (= (bvashr s (_ bv14 26)) t) (= (bvashr s (_ bv15 26)) t) (= (bvashr s (_ bv16 26)) t) (= (bvashr s (_ bv17 26)) t) (= (bvashr s (_ bv18 26)) t) (= (bvashr s (_ bv19 26)) t) (= (bvashr s (_ bv20 26)) t) (= (bvashr s (_ bv21 26)) t) (= (bvashr s (_ bv22 26)) t) (= (bvashr s (_ bv23 26)) t) (= (bvashr s (_ bv24 26)) t) (= (bvashr s (_ bv25 26)) t) (= (bvashr s (_ bv26 26)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 26))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 26))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
