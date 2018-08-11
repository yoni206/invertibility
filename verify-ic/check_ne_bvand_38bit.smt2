(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 38))
(declare-fun t () (_ BitVec 38))

(define-fun udivtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) (bvnot (_ bv0 38)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) a (bvurem a b))
)
(define-fun min () (_ BitVec 38)
  (bvnot (bvlshr (bvnot (_ bv0 38)) (_ bv1 38)))
)
(define-fun max () (_ BitVec 38)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 38)) (t (_ BitVec 38))) Bool
(or (distinct s (_ bv0 38)) (distinct t (_ bv0 38)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 38))) (distinct (bvand x s) t)))
  (=> (exists ((x (_ BitVec 38))) (distinct (bvand x s) t)) (SC s t))
  )
 )
)
(check-sat)
