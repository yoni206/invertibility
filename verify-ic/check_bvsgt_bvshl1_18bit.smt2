(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 18))
(declare-fun t () (_ BitVec 18))

(define-fun udivtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) (bvnot (_ bv0 18)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) a (bvurem a b))
)
(define-fun min () (_ BitVec 18)
  (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18)))
)
(define-fun max () (_ BitVec 18)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 18)) (t (_ BitVec 18))) Bool
(or  (bvsgt (bvshl s (_ bv0 18)) t) (bvsgt (bvshl s (_ bv1 18)) t) (bvsgt (bvshl s (_ bv2 18)) t) (bvsgt (bvshl s (_ bv3 18)) t) (bvsgt (bvshl s (_ bv4 18)) t) (bvsgt (bvshl s (_ bv5 18)) t) (bvsgt (bvshl s (_ bv6 18)) t) (bvsgt (bvshl s (_ bv7 18)) t) (bvsgt (bvshl s (_ bv8 18)) t) (bvsgt (bvshl s (_ bv9 18)) t) (bvsgt (bvshl s (_ bv10 18)) t) (bvsgt (bvshl s (_ bv11 18)) t) (bvsgt (bvshl s (_ bv12 18)) t) (bvsgt (bvshl s (_ bv13 18)) t) (bvsgt (bvshl s (_ bv14 18)) t) (bvsgt (bvshl s (_ bv15 18)) t) (bvsgt (bvshl s (_ bv16 18)) t) (bvsgt (bvshl s (_ bv17 18)) t) (bvsgt (bvshl s (_ bv18 18)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 18))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 18))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
