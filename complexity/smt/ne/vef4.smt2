(set-logic BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))

(define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) (bvnot (_ bv0 4)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) a (bvurem a b))
)
(define-fun min () (_ BitVec 4)
  (bvnot (bvlshr (bvnot (_ bv0 4)) (_ bv1 4)))
)
(define-fun max () (_ BitVec 4)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool (not (= (bvor (bvshl (_ bv7 4) s) t) (_ bv0 4))))

(define-fun l ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 4))) (l x s t)))
  (=> (exists ((x (_ BitVec 4))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
