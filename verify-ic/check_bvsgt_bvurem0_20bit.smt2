(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 20))
(declare-fun t () (_ BitVec 20))

(define-fun udivtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) (bvnot (_ bv0 20)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) a (bvurem a b))
)
(define-fun min () (_ BitVec 20)
  (bvnot (bvlshr (bvnot (_ bv0 20)) (_ bv1 20)))
)
(define-fun max () (_ BitVec 20)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 20)) (t (_ BitVec 20))) Bool
(and (and (=> (bvsgt s (_ bv0 20)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 20)) (distinct t max))) (or (distinct t (_ bv0 20)) (distinct s (_ bv1 20))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 20))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 20))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
