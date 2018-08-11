(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))

(define-fun udivtotal ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 2)
  (ite (= b (_ bv0 2)) (bvnot (_ bv0 2)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 2)
  (ite (= b (_ bv0 2)) a (bvurem a b))
)
(define-fun min () (_ BitVec 2)
  (bvnot (bvlshr (bvnot (_ bv0 2)) (_ bv1 2)))
)
(define-fun max () (_ BitVec 2)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 2)) (t (_ BitVec 2))) Bool
true
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 2))) (bvsge (bvnot x) t)))
  (=> (exists ((x (_ BitVec 2))) (bvsge (bvnot x) t)) (SC s t))
  )
 )
)
(check-sat)
