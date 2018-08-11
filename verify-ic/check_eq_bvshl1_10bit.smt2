(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 10))
(declare-fun t () (_ BitVec 10))

(define-fun udivtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) (bvnot (_ bv0 10)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) a (bvurem a b))
)
(define-fun min () (_ BitVec 10)
  (bvnot (bvlshr (bvnot (_ bv0 10)) (_ bv1 10)))
)
(define-fun max () (_ BitVec 10)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 10)) (t (_ BitVec 10))) Bool
(or  (= (bvshl s (_ bv0 10)) t) (= (bvshl s (_ bv1 10)) t) (= (bvshl s (_ bv2 10)) t) (= (bvshl s (_ bv3 10)) t) (= (bvshl s (_ bv4 10)) t) (= (bvshl s (_ bv5 10)) t) (= (bvshl s (_ bv6 10)) t) (= (bvshl s (_ bv7 10)) t) (= (bvshl s (_ bv8 10)) t) (= (bvshl s (_ bv9 10)) t) (= (bvshl s (_ bv10 10)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 10))) (= (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 10))) (= (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
