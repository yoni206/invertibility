(set-logic BV)
(declare-fun s () (_ BitVec 84))
(declare-fun t () (_ BitVec 84))

(define-fun udivtotal ((a (_ BitVec 84)) (b (_ BitVec 84))) (_ BitVec 84)
  (ite (= b (_ bv0 84)) (bvnot (_ bv0 84)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 84)) (b (_ BitVec 84))) (_ BitVec 84)
  (ite (= b (_ bv0 84)) a (bvurem a b))
)
(define-fun min () (_ BitVec 84)
  (bvnot (bvlshr (bvnot (_ bv0 84)) (_ bv1 84)))
)
(define-fun max () (_ BitVec 84)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 84)) (t (_ BitVec 84))) Bool (= (bvand (bvshl (bvnot (_ bv0000 84)) s) t) t))

(define-fun l ((x (_ BitVec 84)) (s (_ BitVec 84)) (t (_ BitVec 84))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 84))) (l x s t)))
  (=> (exists ((x (_ BitVec 84))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
