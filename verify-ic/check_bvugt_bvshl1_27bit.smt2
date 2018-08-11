(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun t () (_ BitVec 27))

(define-fun udivtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) (bvnot (_ bv0 27)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) a (bvurem a b))
)
(define-fun min () (_ BitVec 27)
  (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27)))
)
(define-fun max () (_ BitVec 27)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 27)) (t (_ BitVec 27))) Bool
(or  (bvugt (bvshl s (_ bv0 27)) t) (bvugt (bvshl s (_ bv1 27)) t) (bvugt (bvshl s (_ bv2 27)) t) (bvugt (bvshl s (_ bv3 27)) t) (bvugt (bvshl s (_ bv4 27)) t) (bvugt (bvshl s (_ bv5 27)) t) (bvugt (bvshl s (_ bv6 27)) t) (bvugt (bvshl s (_ bv7 27)) t) (bvugt (bvshl s (_ bv8 27)) t) (bvugt (bvshl s (_ bv9 27)) t) (bvugt (bvshl s (_ bv10 27)) t) (bvugt (bvshl s (_ bv11 27)) t) (bvugt (bvshl s (_ bv12 27)) t) (bvugt (bvshl s (_ bv13 27)) t) (bvugt (bvshl s (_ bv14 27)) t) (bvugt (bvshl s (_ bv15 27)) t) (bvugt (bvshl s (_ bv16 27)) t) (bvugt (bvshl s (_ bv17 27)) t) (bvugt (bvshl s (_ bv18 27)) t) (bvugt (bvshl s (_ bv19 27)) t) (bvugt (bvshl s (_ bv20 27)) t) (bvugt (bvshl s (_ bv21 27)) t) (bvugt (bvshl s (_ bv22 27)) t) (bvugt (bvshl s (_ bv23 27)) t) (bvugt (bvshl s (_ bv24 27)) t) (bvugt (bvshl s (_ bv25 27)) t) (bvugt (bvshl s (_ bv26 27)) t) (bvugt (bvshl s (_ bv27 27)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 27))) (bvugt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 27))) (bvugt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
