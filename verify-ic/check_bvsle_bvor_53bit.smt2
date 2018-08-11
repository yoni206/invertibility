(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 53))
(declare-fun t () (_ BitVec 53))

(define-fun udivtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) (bvnot (_ bv0 53)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) a (bvurem a b))
)
(define-fun min () (_ BitVec 53)
  (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53)))
)
(define-fun max () (_ BitVec 53)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 53)) (t (_ BitVec 53))) Bool
(bvsge t (bvor s min))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 53))) (bvsle (bvor x s) t)))
  (=> (exists ((x (_ BitVec 53))) (bvsle (bvor x s) t)) (SC s t))
  )
 )
)
(check-sat)
