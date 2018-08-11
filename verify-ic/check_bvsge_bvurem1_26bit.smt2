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
(and (=> (bvsge s (_ bv0 26)) (bvsge s t)) (=> (and (bvslt s (_ bv0 26)) (bvsge t (_ bv0 26))) (bvugt (bvsub s t) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 26))) (bvsge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 26))) (bvsge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
