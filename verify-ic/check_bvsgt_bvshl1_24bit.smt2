(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 24))
(declare-fun t () (_ BitVec 24))

(define-fun udivtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) (bvnot (_ bv0 24)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) a (bvurem a b))
)
(define-fun min () (_ BitVec 24)
  (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24)))
)
(define-fun max () (_ BitVec 24)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 24)) (t (_ BitVec 24))) Bool
(or  (bvsgt (bvshl s (_ bv0 24)) t) (bvsgt (bvshl s (_ bv1 24)) t) (bvsgt (bvshl s (_ bv2 24)) t) (bvsgt (bvshl s (_ bv3 24)) t) (bvsgt (bvshl s (_ bv4 24)) t) (bvsgt (bvshl s (_ bv5 24)) t) (bvsgt (bvshl s (_ bv6 24)) t) (bvsgt (bvshl s (_ bv7 24)) t) (bvsgt (bvshl s (_ bv8 24)) t) (bvsgt (bvshl s (_ bv9 24)) t) (bvsgt (bvshl s (_ bv10 24)) t) (bvsgt (bvshl s (_ bv11 24)) t) (bvsgt (bvshl s (_ bv12 24)) t) (bvsgt (bvshl s (_ bv13 24)) t) (bvsgt (bvshl s (_ bv14 24)) t) (bvsgt (bvshl s (_ bv15 24)) t) (bvsgt (bvshl s (_ bv16 24)) t) (bvsgt (bvshl s (_ bv17 24)) t) (bvsgt (bvshl s (_ bv18 24)) t) (bvsgt (bvshl s (_ bv19 24)) t) (bvsgt (bvshl s (_ bv20 24)) t) (bvsgt (bvshl s (_ bv21 24)) t) (bvsgt (bvshl s (_ bv22 24)) t) (bvsgt (bvshl s (_ bv23 24)) t) (bvsgt (bvshl s (_ bv24 24)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 24))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 24))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
