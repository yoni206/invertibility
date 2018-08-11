(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))

(define-fun udivtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) (bvnot (_ bv0 16)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) a (bvurem a b))
)
(define-fun min () (_ BitVec 16)
  (bvnot (bvlshr (bvnot (_ bv0 16)) (_ bv1 16)))
)
(define-fun max () (_ BitVec 16)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 16)) (t (_ BitVec 16))) Bool
(or  (bvsgt (bvshl s (_ bv0 16)) t) (bvsgt (bvshl s (_ bv1 16)) t) (bvsgt (bvshl s (_ bv2 16)) t) (bvsgt (bvshl s (_ bv3 16)) t) (bvsgt (bvshl s (_ bv4 16)) t) (bvsgt (bvshl s (_ bv5 16)) t) (bvsgt (bvshl s (_ bv6 16)) t) (bvsgt (bvshl s (_ bv7 16)) t) (bvsgt (bvshl s (_ bv8 16)) t) (bvsgt (bvshl s (_ bv9 16)) t) (bvsgt (bvshl s (_ bv10 16)) t) (bvsgt (bvshl s (_ bv11 16)) t) (bvsgt (bvshl s (_ bv12 16)) t) (bvsgt (bvshl s (_ bv13 16)) t) (bvsgt (bvshl s (_ bv14 16)) t) (bvsgt (bvshl s (_ bv15 16)) t) (bvsgt (bvshl s (_ bv16 16)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 16))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 16))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
