(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 46))
(declare-fun t () (_ BitVec 46))

(define-fun udivtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) (bvnot (_ bv0 46)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) a (bvurem a b))
)
(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 46)) (t (_ BitVec 46))) Bool
(=> (bvsle t (_ bv0 46)) (bvslt (udivtotal min s) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 46))) (bvslt (udivtotal x s) t)))
  (=> (exists ((x (_ BitVec 46))) (bvslt (udivtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
