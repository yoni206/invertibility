(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 19))
(declare-fun t () (_ BitVec 19))

(define-fun udivtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) (bvnot (_ bv0 19)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) a (bvurem a b))
)
(define-fun min () (_ BitVec 19)
  (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19)))
)
(define-fun max () (_ BitVec 19)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 19)) (t (_ BitVec 19))) Bool
(or  (bvsgt (bvshl s (_ bv0 19)) t) (bvsgt (bvshl s (_ bv1 19)) t) (bvsgt (bvshl s (_ bv2 19)) t) (bvsgt (bvshl s (_ bv3 19)) t) (bvsgt (bvshl s (_ bv4 19)) t) (bvsgt (bvshl s (_ bv5 19)) t) (bvsgt (bvshl s (_ bv6 19)) t) (bvsgt (bvshl s (_ bv7 19)) t) (bvsgt (bvshl s (_ bv8 19)) t) (bvsgt (bvshl s (_ bv9 19)) t) (bvsgt (bvshl s (_ bv10 19)) t) (bvsgt (bvshl s (_ bv11 19)) t) (bvsgt (bvshl s (_ bv12 19)) t) (bvsgt (bvshl s (_ bv13 19)) t) (bvsgt (bvshl s (_ bv14 19)) t) (bvsgt (bvshl s (_ bv15 19)) t) (bvsgt (bvshl s (_ bv16 19)) t) (bvsgt (bvshl s (_ bv17 19)) t) (bvsgt (bvshl s (_ bv18 19)) t) (bvsgt (bvshl s (_ bv19 19)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 19))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 19))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
