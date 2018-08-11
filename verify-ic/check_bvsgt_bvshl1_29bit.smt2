(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 29))
(declare-fun t () (_ BitVec 29))

(define-fun udivtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) (bvnot (_ bv0 29)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) a (bvurem a b))
)
(define-fun min () (_ BitVec 29)
  (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29)))
)
(define-fun max () (_ BitVec 29)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 29)) (t (_ BitVec 29))) Bool
(or  (bvsgt (bvshl s (_ bv0 29)) t) (bvsgt (bvshl s (_ bv1 29)) t) (bvsgt (bvshl s (_ bv2 29)) t) (bvsgt (bvshl s (_ bv3 29)) t) (bvsgt (bvshl s (_ bv4 29)) t) (bvsgt (bvshl s (_ bv5 29)) t) (bvsgt (bvshl s (_ bv6 29)) t) (bvsgt (bvshl s (_ bv7 29)) t) (bvsgt (bvshl s (_ bv8 29)) t) (bvsgt (bvshl s (_ bv9 29)) t) (bvsgt (bvshl s (_ bv10 29)) t) (bvsgt (bvshl s (_ bv11 29)) t) (bvsgt (bvshl s (_ bv12 29)) t) (bvsgt (bvshl s (_ bv13 29)) t) (bvsgt (bvshl s (_ bv14 29)) t) (bvsgt (bvshl s (_ bv15 29)) t) (bvsgt (bvshl s (_ bv16 29)) t) (bvsgt (bvshl s (_ bv17 29)) t) (bvsgt (bvshl s (_ bv18 29)) t) (bvsgt (bvshl s (_ bv19 29)) t) (bvsgt (bvshl s (_ bv20 29)) t) (bvsgt (bvshl s (_ bv21 29)) t) (bvsgt (bvshl s (_ bv22 29)) t) (bvsgt (bvshl s (_ bv23 29)) t) (bvsgt (bvshl s (_ bv24 29)) t) (bvsgt (bvshl s (_ bv25 29)) t) (bvsgt (bvshl s (_ bv26 29)) t) (bvsgt (bvshl s (_ bv27 29)) t) (bvsgt (bvshl s (_ bv28 29)) t) (bvsgt (bvshl s (_ bv29 29)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 29))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 29))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
