(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))

(define-fun udivtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) (bvnot (_ bv0 16)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) a (bvurem a b))
)
(define-fun min () (_ BitVec 16)
  (bvnot (bvlshr (bvnot (_ bv0 16)) (_ bv1 16)))
)
(define-fun max () (_ BitVec 16)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 16)) (t (_ BitVec 16))) Bool
true
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 16))) (bvule (bvnot x) t)))
  (=> (exists ((x (_ BitVec 16))) (bvule (bvnot x) t)) (SC s t))
  )
 )
)
(check-sat)
