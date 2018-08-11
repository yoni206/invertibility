(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 23))
(declare-fun t () (_ BitVec 23))

(define-fun udivtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) (bvnot (_ bv0 23)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) a (bvurem a b))
)
(define-fun min () (_ BitVec 23)
  (bvnot (bvlshr (bvnot (_ bv0 23)) (_ bv1 23)))
)
(define-fun max () (_ BitVec 23)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 23)) (t (_ BitVec 23))) Bool
(bvslt t (bvlshr (bvshl max s) s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 23))) (bvsgt (bvlshr x s) t)))
  (=> (exists ((x (_ BitVec 23))) (bvsgt (bvlshr x s) t)) (SC s t))
  )
 )
)
(check-sat)
