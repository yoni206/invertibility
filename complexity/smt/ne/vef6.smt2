(set-logic BV)
(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))

(define-fun udivtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) (bvnot (_ bv0 6)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) a (bvurem a b))
)
(define-fun min () (_ BitVec 6)
  (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6)))
)
(define-fun max () (_ BitVec 6)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 6)) (t (_ BitVec 6))) Bool (not (= (bvor (bvshl (_ bv7 6) s) t) (_ bv0 6))))

(define-fun l ((x (_ BitVec 6)) (s (_ BitVec 6)) (t (_ BitVec 6))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 6))) (l x s t)))
  (=> (exists ((x (_ BitVec 6))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
