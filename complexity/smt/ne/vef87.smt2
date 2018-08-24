(set-logic BV)
(declare-fun s () (_ BitVec 87))
(declare-fun t () (_ BitVec 87))

(define-fun udivtotal ((a (_ BitVec 87)) (b (_ BitVec 87))) (_ BitVec 87)
  (ite (= b (_ bv0 87)) (bvnot (_ bv0 87)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 87)) (b (_ BitVec 87))) (_ BitVec 87)
  (ite (= b (_ bv0 87)) a (bvurem a b))
)
(define-fun min () (_ BitVec 87)
  (bvnot (bvlshr (bvnot (_ bv0 87)) (_ bv1 87)))
)
(define-fun max () (_ BitVec 87)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 87)) (t (_ BitVec 87))) Bool (not (= (bvor (bvshl (_ bv7 87) s) t) (_ bv0 87))))

(define-fun l ((x (_ BitVec 87)) (s (_ BitVec 87)) (t (_ BitVec 87))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 87))) (l x s t)))
  (=> (exists ((x (_ BitVec 87))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
