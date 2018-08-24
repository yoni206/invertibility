(set-logic BV)
(declare-fun s () (_ BitVec 95))
(declare-fun t () (_ BitVec 95))

(define-fun udivtotal ((a (_ BitVec 95)) (b (_ BitVec 95))) (_ BitVec 95)
  (ite (= b (_ bv0 95)) (bvnot (_ bv0 95)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 95)) (b (_ BitVec 95))) (_ BitVec 95)
  (ite (= b (_ bv0 95)) a (bvurem a b))
)
(define-fun min () (_ BitVec 95)
  (bvnot (bvlshr (bvnot (_ bv0 95)) (_ bv1 95)))
)
(define-fun max () (_ BitVec 95)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 95)) (t (_ BitVec 95))) Bool (not (= (bvor (bvshl (_ bv7 95) s) t) (_ bv0 95))))

(define-fun l ((x (_ BitVec 95)) (s (_ BitVec 95)) (t (_ BitVec 95))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 95))) (l x s t)))
  (=> (exists ((x (_ BitVec 95))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
