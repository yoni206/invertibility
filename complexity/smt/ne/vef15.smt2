(set-logic BV)
(declare-fun s () (_ BitVec 15))
(declare-fun t () (_ BitVec 15))

(define-fun udivtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) (bvnot (_ bv0 15)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) a (bvurem a b))
)
(define-fun min () (_ BitVec 15)
  (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15)))
)
(define-fun max () (_ BitVec 15)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 15)) (t (_ BitVec 15))) Bool (not (= (bvor (bvshl (_ bv7 15) s) t) (_ bv0 15))))

(define-fun l ((x (_ BitVec 15)) (s (_ BitVec 15)) (t (_ BitVec 15))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 15))) (l x s t)))
  (=> (exists ((x (_ BitVec 15))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
