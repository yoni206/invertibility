(set-logic BV)
(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)
(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 35)) (t (_ BitVec 35))) Bool (not (= (bvor (bvshl (_ bv7 35) s) t) (_ bv0 35))))

(define-fun l ((x (_ BitVec 35)) (s (_ BitVec 35)) (t (_ BitVec 35))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (l x s t)))
  (=> (exists ((x (_ BitVec 35))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
