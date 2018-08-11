(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 19))
(declare-fun t () (_ BitVec 19))

(define-fun udivtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) (bvnot (_ bv0 19)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) a (bvurem a b))
)
(define-fun min () (_ BitVec 19)
  (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19)))
)
(define-fun max () (_ BitVec 19)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 19)) (t (_ BitVec 19))) Bool
(and (and (=> (bvsgt s (_ bv0 19)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 19)) (distinct t max))) (or (distinct t (_ bv0 19)) (distinct s (_ bv1 19))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 19))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 19))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
