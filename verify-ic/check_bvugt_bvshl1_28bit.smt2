(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 28))
(declare-fun t () (_ BitVec 28))

(define-fun udivtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) (bvnot (_ bv0 28)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) a (bvurem a b))
)
(define-fun min () (_ BitVec 28)
  (bvnot (bvlshr (bvnot (_ bv0 28)) (_ bv1 28)))
)
(define-fun max () (_ BitVec 28)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 28)) (t (_ BitVec 28))) Bool
(or  (bvugt (bvshl s (_ bv0 28)) t) (bvugt (bvshl s (_ bv1 28)) t) (bvugt (bvshl s (_ bv2 28)) t) (bvugt (bvshl s (_ bv3 28)) t) (bvugt (bvshl s (_ bv4 28)) t) (bvugt (bvshl s (_ bv5 28)) t) (bvugt (bvshl s (_ bv6 28)) t) (bvugt (bvshl s (_ bv7 28)) t) (bvugt (bvshl s (_ bv8 28)) t) (bvugt (bvshl s (_ bv9 28)) t) (bvugt (bvshl s (_ bv10 28)) t) (bvugt (bvshl s (_ bv11 28)) t) (bvugt (bvshl s (_ bv12 28)) t) (bvugt (bvshl s (_ bv13 28)) t) (bvugt (bvshl s (_ bv14 28)) t) (bvugt (bvshl s (_ bv15 28)) t) (bvugt (bvshl s (_ bv16 28)) t) (bvugt (bvshl s (_ bv17 28)) t) (bvugt (bvshl s (_ bv18 28)) t) (bvugt (bvshl s (_ bv19 28)) t) (bvugt (bvshl s (_ bv20 28)) t) (bvugt (bvshl s (_ bv21 28)) t) (bvugt (bvshl s (_ bv22 28)) t) (bvugt (bvshl s (_ bv23 28)) t) (bvugt (bvshl s (_ bv24 28)) t) (bvugt (bvshl s (_ bv25 28)) t) (bvugt (bvshl s (_ bv26 28)) t) (bvugt (bvshl s (_ bv27 28)) t) (bvugt (bvshl s (_ bv28 28)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 28))) (bvugt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 28))) (bvugt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
