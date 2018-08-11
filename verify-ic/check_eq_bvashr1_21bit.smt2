(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 21))
(declare-fun t () (_ BitVec 21))

(define-fun udivtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) (bvnot (_ bv0 21)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) a (bvurem a b))
)
(define-fun min () (_ BitVec 21)
  (bvnot (bvlshr (bvnot (_ bv0 21)) (_ bv1 21)))
)
(define-fun max () (_ BitVec 21)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 21)) (t (_ BitVec 21))) Bool
(or  (= (bvashr s (_ bv0 21)) t) (= (bvashr s (_ bv1 21)) t) (= (bvashr s (_ bv2 21)) t) (= (bvashr s (_ bv3 21)) t) (= (bvashr s (_ bv4 21)) t) (= (bvashr s (_ bv5 21)) t) (= (bvashr s (_ bv6 21)) t) (= (bvashr s (_ bv7 21)) t) (= (bvashr s (_ bv8 21)) t) (= (bvashr s (_ bv9 21)) t) (= (bvashr s (_ bv10 21)) t) (= (bvashr s (_ bv11 21)) t) (= (bvashr s (_ bv12 21)) t) (= (bvashr s (_ bv13 21)) t) (= (bvashr s (_ bv14 21)) t) (= (bvashr s (_ bv15 21)) t) (= (bvashr s (_ bv16 21)) t) (= (bvashr s (_ bv17 21)) t) (= (bvashr s (_ bv18 21)) t) (= (bvashr s (_ bv19 21)) t) (= (bvashr s (_ bv20 21)) t) (= (bvashr s (_ bv21 21)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 21))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 21))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
