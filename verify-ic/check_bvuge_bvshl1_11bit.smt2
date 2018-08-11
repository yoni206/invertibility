(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun t () (_ BitVec 11))

(define-fun udivtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) (bvnot (_ bv0 11)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) a (bvurem a b))
)
(define-fun min () (_ BitVec 11)
  (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11)))
)
(define-fun max () (_ BitVec 11)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 11)) (t (_ BitVec 11))) Bool
(or  (bvuge (bvshl s (_ bv0 11)) t) (bvuge (bvshl s (_ bv1 11)) t) (bvuge (bvshl s (_ bv2 11)) t) (bvuge (bvshl s (_ bv3 11)) t) (bvuge (bvshl s (_ bv4 11)) t) (bvuge (bvshl s (_ bv5 11)) t) (bvuge (bvshl s (_ bv6 11)) t) (bvuge (bvshl s (_ bv7 11)) t) (bvuge (bvshl s (_ bv8 11)) t) (bvuge (bvshl s (_ bv9 11)) t) (bvuge (bvshl s (_ bv10 11)) t) (bvuge (bvshl s (_ bv11 11)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 11))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 11))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
