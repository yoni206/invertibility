(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 50))
(declare-fun t () (_ BitVec 50))

(define-fun udivtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) (bvnot (_ bv0 50)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) a (bvurem a b))
)
(define-fun min () (_ BitVec 50)
  (bvnot (bvlshr (bvnot (_ bv0 50)) (_ bv1 50)))
)
(define-fun max () (_ BitVec 50)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 50)) (t (_ BitVec 50))) Bool
(and (and (=> (bvsgt s (_ bv0 50)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 50)) (distinct t max))) (or (distinct t (_ bv0 50)) (distinct s (_ bv1 50))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 50))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 50))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
