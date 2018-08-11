(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 26))
(declare-fun t () (_ BitVec 26))

(define-fun udivtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) (bvnot (_ bv0 26)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) a (bvurem a b))
)
(define-fun min () (_ BitVec 26)
  (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26)))
)
(define-fun max () (_ BitVec 26)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 26)) (t (_ BitVec 26))) Bool
(bvsge (bvand (bvshl max s) max) t)
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 26))) (bvsge (bvshl x s) t)))
  (=> (exists ((x (_ BitVec 26))) (bvsge (bvshl x s) t)) (SC s t))
  )
 )
)
(check-sat)
