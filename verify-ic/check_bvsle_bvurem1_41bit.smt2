(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 41))
(declare-fun t () (_ BitVec 41))

(define-fun udivtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) (bvnot (_ bv0 41)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) a (bvurem a b))
)
(define-fun min () (_ BitVec 41)
  (bvnot (bvlshr (bvnot (_ bv0 41)) (_ bv1 41)))
)
(define-fun max () (_ BitVec 41)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 41)) (t (_ BitVec 41))) Bool
(or (bvult t min) (bvsge t s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 41))) (bvsle (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 41))) (bvsle (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
