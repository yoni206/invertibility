(set-logic BV)
(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))

(define-fun udivtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) (bvnot (_ bv0 3)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) a (bvurem a b))
)
(define-fun min () (_ BitVec 3)
  (bvnot (bvlshr (bvnot (_ bv0 3)) (_ bv1 3)))
)
(define-fun max () (_ BitVec 3)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 3)) (t (_ BitVec 3))) Bool (not (= (bvor (bvshl (_ bv7 3) s) t) (_ bv0 3))))

(define-fun l ((x (_ BitVec 3)) (s (_ BitVec 3)) (t (_ BitVec 3))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 3))) (l x s t)))
  (=> (exists ((x (_ BitVec 3))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
