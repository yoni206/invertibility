(set-logic BV)
(declare-fun s () (_ BitVec 78))
(declare-fun t () (_ BitVec 78))

(define-fun udivtotal ((a (_ BitVec 78)) (b (_ BitVec 78))) (_ BitVec 78)
  (ite (= b (_ bv0 78)) (bvnot (_ bv0 78)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 78)) (b (_ BitVec 78))) (_ BitVec 78)
  (ite (= b (_ bv0 78)) a (bvurem a b))
)
(define-fun min () (_ BitVec 78)
  (bvnot (bvlshr (bvnot (_ bv0 78)) (_ bv1 78)))
)
(define-fun max () (_ BitVec 78)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 78)) (t (_ BitVec 78))) Bool (= (bvand (bvshl (bvnot (_ bv0000 78)) s) t) t))

(define-fun l ((x (_ BitVec 78)) (s (_ BitVec 78)) (t (_ BitVec 78))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 78))) (l x s t)))
  (=> (exists ((x (_ BitVec 78))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
