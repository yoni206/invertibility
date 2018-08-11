(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)
(define-fun min () (_ BitVec 64)
  (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64)))
)
(define-fun max () (_ BitVec 64)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 64)) (t (_ BitVec 64))) Bool
(and (not (and (not (bvult s t)) (bvslt s (_ bv0 64)))) (not (= t (_ bv0 64))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 64))) (bvult (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 64))) (bvult (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
