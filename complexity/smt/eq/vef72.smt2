(set-logic BV)
(declare-fun s () (_ BitVec 72))
(declare-fun t () (_ BitVec 72))

(define-fun udivtotal ((a (_ BitVec 72)) (b (_ BitVec 72))) (_ BitVec 72)
  (ite (= b (_ bv0 72)) (bvnot (_ bv0 72)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 72)) (b (_ BitVec 72))) (_ BitVec 72)
  (ite (= b (_ bv0 72)) a (bvurem a b))
)
(define-fun min () (_ BitVec 72)
  (bvnot (bvlshr (bvnot (_ bv0 72)) (_ bv1 72)))
)
(define-fun max () (_ BitVec 72)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 72)) (t (_ BitVec 72))) Bool (= (bvand (bvshl (bvnot (_ bv0000 72)) s) t) t))

(define-fun l ((x (_ BitVec 72)) (s (_ BitVec 72)) (t (_ BitVec 72))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 72))) (l x s t)))
  (=> (exists ((x (_ BitVec 72))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
