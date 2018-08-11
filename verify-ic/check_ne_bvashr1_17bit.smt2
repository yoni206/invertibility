(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)
(define-fun min () (_ BitVec 17)
  (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17)))
)
(define-fun max () (_ BitVec 17)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 17)) (t (_ BitVec 17))) Bool
(and (or (not (= t (_ bv0 17))) (not (= s (_ bv0 17)))) (or (not (= t (bvnot (_ bv0 17)))) (not (= s (bvnot (_ bv0 17))))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 17))) (distinct (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 17))) (distinct (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
