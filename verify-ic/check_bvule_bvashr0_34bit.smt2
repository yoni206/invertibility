(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 34))
(declare-fun t () (_ BitVec 34))

(define-fun udivtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) (bvnot (_ bv0 34)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) a (bvurem a b))
)
(define-fun min () (_ BitVec 34)
  (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34)))
)
(define-fun max () (_ BitVec 34)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 34)) (t (_ BitVec 34))) Bool
true
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 34))) (bvule (bvashr x s) t)))
  (=> (exists ((x (_ BitVec 34))) (bvule (bvashr x s) t)) (SC s t))
  )
 )
)
(check-sat)
