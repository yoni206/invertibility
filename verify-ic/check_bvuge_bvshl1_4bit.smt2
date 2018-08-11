(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) (bvnot (_ bv0 4)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) a (bvurem a b))
)
(define-fun min () (_ BitVec 4)
  (bvnot (bvlshr (bvnot (_ bv0 4)) (_ bv1 4)))
)
(define-fun max () (_ BitVec 4)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool
(or  (bvuge (bvshl s (_ bv0 4)) t) (bvuge (bvshl s (_ bv1 4)) t) (bvuge (bvshl s (_ bv2 4)) t) (bvuge (bvshl s (_ bv3 4)) t) (bvuge (bvshl s (_ bv4 4)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 4))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 4))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
