(set-logic BV)
(declare-fun s () (_ BitVec 71))
(declare-fun t () (_ BitVec 71))

(define-fun udivtotal ((a (_ BitVec 71)) (b (_ BitVec 71))) (_ BitVec 71)
  (ite (= b (_ bv0 71)) (bvnot (_ bv0 71)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 71)) (b (_ BitVec 71))) (_ BitVec 71)
  (ite (= b (_ bv0 71)) a (bvurem a b))
)
(define-fun min () (_ BitVec 71)
  (bvnot (bvlshr (bvnot (_ bv0 71)) (_ bv1 71)))
)
(define-fun max () (_ BitVec 71)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 71)) (t (_ BitVec 71))) Bool (= (bvand (bvshl (bvnot (_ bv0000 71)) s) t) t))

(define-fun l ((x (_ BitVec 71)) (s (_ BitVec 71)) (t (_ BitVec 71))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 71))) (l x s t)))
  (=> (exists ((x (_ BitVec 71))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
