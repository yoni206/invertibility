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
(or (bvsge t (_ bv0 42)) (bvsge t s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 42))) (bvsle (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 42))) (bvsle (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
