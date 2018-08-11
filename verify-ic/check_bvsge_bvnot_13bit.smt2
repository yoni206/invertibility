(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 13))
(declare-fun t () (_ BitVec 13))

(define-fun udivtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) (bvnot (_ bv0 13)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) a (bvurem a b))
)
(define-fun min () (_ BitVec 13)
  (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13)))
)
(define-fun max () (_ BitVec 13)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 13)) (t (_ BitVec 13))) Bool
true
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 13))) (bvsge (bvnot x) t)))
  (=> (exists ((x (_ BitVec 13))) (bvsge (bvnot x) t)) (SC s t))
  )
 )
)
(check-sat)
