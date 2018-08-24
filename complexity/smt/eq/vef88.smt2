(set-logic BV)
(declare-fun s () (_ BitVec 88))
(declare-fun t () (_ BitVec 88))

(define-fun udivtotal ((a (_ BitVec 88)) (b (_ BitVec 88))) (_ BitVec 88)
  (ite (= b (_ bv0 88)) (bvnot (_ bv0 88)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 88)) (b (_ BitVec 88))) (_ BitVec 88)
  (ite (= b (_ bv0 88)) a (bvurem a b))
)
(define-fun min () (_ BitVec 88)
  (bvnot (bvlshr (bvnot (_ bv0 88)) (_ bv1 88)))
)
(define-fun max () (_ BitVec 88)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 88)) (t (_ BitVec 88))) Bool (= (bvand (bvshl (bvnot (_ bv0000 88)) s) t) t))

(define-fun l ((x (_ BitVec 88)) (s (_ BitVec 88)) (t (_ BitVec 88))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 88))) (l x s t)))
  (=> (exists ((x (_ BitVec 88))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
