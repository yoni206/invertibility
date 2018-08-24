(set-logic BV)
(declare-fun s () (_ BitVec 28))
(declare-fun t () (_ BitVec 28))

(define-fun udivtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) (bvnot (_ bv0 28)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) a (bvurem a b))
)
(define-fun min () (_ BitVec 28)
  (bvnot (bvlshr (bvnot (_ bv0 28)) (_ bv1 28)))
)
(define-fun max () (_ BitVec 28)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 28)) (t (_ BitVec 28))) Bool (not (= (bvor (bvshl (_ bv7 28) s) t) (_ bv0 28))))

(define-fun l ((x (_ BitVec 28)) (s (_ BitVec 28)) (t (_ BitVec 28))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 28))) (l x s t)))
  (=> (exists ((x (_ BitVec 28))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
