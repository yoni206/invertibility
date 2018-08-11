(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 42))
(declare-fun t () (_ BitVec 42))

(define-fun udivtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) (bvnot (_ bv0 42)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) a (bvurem a b))
)
(define-fun min () (_ BitVec 42)
  (bvnot (bvlshr (bvnot (_ bv0 42)) (_ bv1 42)))
)
(define-fun max () (_ BitVec 42)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 42)) (t (_ BitVec 42))) Bool
(not (bvult s t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 42))) (bvuge (bvand x s) t)))
  (=> (exists ((x (_ BitVec 42))) (bvuge (bvand x s) t)) (SC s t))
  )
 )
)
(check-sat)
