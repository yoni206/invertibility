(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun t () (_ BitVec 27))

(define-fun udivtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) (bvnot (_ bv0 27)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) a (bvurem a b))
)
(define-fun min () (_ BitVec 27)
  (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27)))
)
(define-fun max () (_ BitVec 27)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 27)) (t (_ BitVec 27))) Bool
(and (and (=> (bvsgt s (_ bv0 27)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 27)) (distinct t max))) (or (distinct t (_ bv0 27)) (distinct s (_ bv1 27))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 27))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 27))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
