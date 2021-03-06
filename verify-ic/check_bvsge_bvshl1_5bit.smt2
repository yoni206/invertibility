(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)
(define-fun min () (_ BitVec 5)
  (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5)))
)
(define-fun max () (_ BitVec 5)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 5)) (t (_ BitVec 5))) Bool
(or  (bvsge (bvshl s (_ bv0 5)) t) (bvsge (bvshl s (_ bv1 5)) t) (bvsge (bvshl s (_ bv2 5)) t) (bvsge (bvshl s (_ bv3 5)) t) (bvsge (bvshl s (_ bv4 5)) t) (bvsge (bvshl s (_ bv5 5)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 5))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 5))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
