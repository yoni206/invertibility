(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))

(define-fun udivtotal ((a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
  (ite (= b (_ bv0 1)) (bvnot (_ bv0 1)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
  (ite (= b (_ bv0 1)) a (bvurem a b))
)
(define-fun min () (_ BitVec 1)
  (bvnot (bvlshr (bvnot (_ bv0 1)) (_ bv1 1)))
)
(define-fun max () (_ BitVec 1)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 1)) (t (_ BitVec 1))) Bool
(and (not (and (not (bvult s t)) (bvslt s (_ bv0 1)))) (not (= t (_ bv0 1))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 1))) (bvult (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 1))) (bvult (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
