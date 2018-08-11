(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 46))
(declare-fun t () (_ BitVec 46))

(define-fun udivtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) (bvnot (_ bv0 46)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) a (bvurem a b))
)
(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 46)) (t (_ BitVec 46))) Bool
(and (and (=> (bvsgt s (_ bv0 46)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 46)) (distinct t max))) (or (distinct t (_ bv0 46)) (distinct s (_ bv1 46))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 46))) (bvsgt (uremtotal x s) t)))
  (=> (exists ((x (_ BitVec 46))) (bvsgt (uremtotal x s) t)) (SC s t))
  )
 )
)
(check-sat)
