(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 12))
(declare-fun t () (_ BitVec 12))

(define-fun udivtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) (bvnot (_ bv0 12)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) a (bvurem a b))
)
(define-fun min () (_ BitVec 12)
  (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12)))
)
(define-fun max () (_ BitVec 12)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 12)) (t (_ BitVec 12))) Bool
(or  (bvuge (bvshl s (_ bv0 12)) t) (bvuge (bvshl s (_ bv1 12)) t) (bvuge (bvshl s (_ bv2 12)) t) (bvuge (bvshl s (_ bv3 12)) t) (bvuge (bvshl s (_ bv4 12)) t) (bvuge (bvshl s (_ bv5 12)) t) (bvuge (bvshl s (_ bv6 12)) t) (bvuge (bvshl s (_ bv7 12)) t) (bvuge (bvshl s (_ bv8 12)) t) (bvuge (bvshl s (_ bv9 12)) t) (bvuge (bvshl s (_ bv10 12)) t) (bvuge (bvshl s (_ bv11 12)) t) (bvuge (bvshl s (_ bv12 12)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 12))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 12))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
