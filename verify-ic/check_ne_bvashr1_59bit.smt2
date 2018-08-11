(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 59))
(declare-fun t () (_ BitVec 59))

(define-fun udivtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) (bvnot (_ bv0 59)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) a (bvurem a b))
)
(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 59)) (t (_ BitVec 59))) Bool
(and (or (not (= t (_ bv0 59))) (not (= s (_ bv0 59)))) (or (not (= t (bvnot (_ bv0 59)))) (not (= s (bvnot (_ bv0 59))))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 59))) (distinct (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 59))) (distinct (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
