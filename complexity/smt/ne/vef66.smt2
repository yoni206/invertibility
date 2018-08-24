(set-logic BV)
(declare-fun s () (_ BitVec 66))
(declare-fun t () (_ BitVec 66))

(define-fun udivtotal ((a (_ BitVec 66)) (b (_ BitVec 66))) (_ BitVec 66)
  (ite (= b (_ bv0 66)) (bvnot (_ bv0 66)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 66)) (b (_ BitVec 66))) (_ BitVec 66)
  (ite (= b (_ bv0 66)) a (bvurem a b))
)
(define-fun min () (_ BitVec 66)
  (bvnot (bvlshr (bvnot (_ bv0 66)) (_ bv1 66)))
)
(define-fun max () (_ BitVec 66)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 66)) (t (_ BitVec 66))) Bool (not (= (bvor (bvshl (_ bv7 66) s) t) (_ bv0 66))))

(define-fun l ((x (_ BitVec 66)) (s (_ BitVec 66)) (t (_ BitVec 66))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 66))) (l x s t)))
  (=> (exists ((x (_ BitVec 66))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
