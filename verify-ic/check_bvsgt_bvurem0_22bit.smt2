(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 22))
(declare-fun t () (_ BitVec 22))

(define-fun udivtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) (bvnot (_ bv0 22)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) a (bvurem a b))
)
(define-fun min () (_ BitVec 22)
  (bvnot (bvlshr (bvnot (_ bv0 22)) (_ bv1 22)))
)
(define-fun max () (_ BitVec 22)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 22)) (t (_ BitVec 22))) Bool
(and (and (=> (bvsgt s (_ bv0 22)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 22)) (distinct t max))) (or (distinct t (_ bv0 22)) (distinct s (_ bv1 22))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 22))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 22))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
