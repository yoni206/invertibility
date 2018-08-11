(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 62))
(declare-fun t () (_ BitVec 62))

(define-fun udivtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) (bvnot (_ bv0 62)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) a (bvurem a b))
)
(define-fun min () (_ BitVec 62)
  (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62)))
)
(define-fun max () (_ BitVec 62)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 62)) (t (_ BitVec 62))) Bool
(bvslt t (bvlshr (bvshl max s) s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 62))) (bvsgt (bvlshr x s) t)))
  (=> (exists ((x (_ BitVec 62))) (bvsgt (bvlshr x s) t)) (SC s t))
  )
 )
)
(check-sat)
