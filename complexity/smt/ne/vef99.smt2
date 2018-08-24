(set-logic BV)
(declare-fun s () (_ BitVec 99))
(declare-fun t () (_ BitVec 99))

(define-fun udivtotal ((a (_ BitVec 99)) (b (_ BitVec 99))) (_ BitVec 99)
  (ite (= b (_ bv0 99)) (bvnot (_ bv0 99)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 99)) (b (_ BitVec 99))) (_ BitVec 99)
  (ite (= b (_ bv0 99)) a (bvurem a b))
)
(define-fun min () (_ BitVec 99)
  (bvnot (bvlshr (bvnot (_ bv0 99)) (_ bv1 99)))
)
(define-fun max () (_ BitVec 99)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 99)) (t (_ BitVec 99))) Bool (not (= (bvor (bvshl (_ bv7 99) s) t) (_ bv0 99))))

(define-fun l ((x (_ BitVec 99)) (s (_ BitVec 99)) (t (_ BitVec 99))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 99))) (l x s t)))
  (=> (exists ((x (_ BitVec 99))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
