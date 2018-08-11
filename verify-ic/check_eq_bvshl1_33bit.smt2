(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 33))
(declare-fun t () (_ BitVec 33))

(define-fun udivtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) (bvnot (_ bv0 33)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) a (bvurem a b))
)
(define-fun min () (_ BitVec 33)
  (bvnot (bvlshr (bvnot (_ bv0 33)) (_ bv1 33)))
)
(define-fun max () (_ BitVec 33)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 33)) (t (_ BitVec 33))) Bool
(or  (= (bvshl s (_ bv0 33)) t) (= (bvshl s (_ bv1 33)) t) (= (bvshl s (_ bv2 33)) t) (= (bvshl s (_ bv3 33)) t) (= (bvshl s (_ bv4 33)) t) (= (bvshl s (_ bv5 33)) t) (= (bvshl s (_ bv6 33)) t) (= (bvshl s (_ bv7 33)) t) (= (bvshl s (_ bv8 33)) t) (= (bvshl s (_ bv9 33)) t) (= (bvshl s (_ bv10 33)) t) (= (bvshl s (_ bv11 33)) t) (= (bvshl s (_ bv12 33)) t) (= (bvshl s (_ bv13 33)) t) (= (bvshl s (_ bv14 33)) t) (= (bvshl s (_ bv15 33)) t) (= (bvshl s (_ bv16 33)) t) (= (bvshl s (_ bv17 33)) t) (= (bvshl s (_ bv18 33)) t) (= (bvshl s (_ bv19 33)) t) (= (bvshl s (_ bv20 33)) t) (= (bvshl s (_ bv21 33)) t) (= (bvshl s (_ bv22 33)) t) (= (bvshl s (_ bv23 33)) t) (= (bvshl s (_ bv24 33)) t) (= (bvshl s (_ bv25 33)) t) (= (bvshl s (_ bv26 33)) t) (= (bvshl s (_ bv27 33)) t) (= (bvshl s (_ bv28 33)) t) (= (bvshl s (_ bv29 33)) t) (= (bvshl s (_ bv30 33)) t) (= (bvshl s (_ bv31 33)) t) (= (bvshl s (_ bv32 33)) t) (= (bvshl s (_ bv33 33)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 33))) (= (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 33))) (= (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
