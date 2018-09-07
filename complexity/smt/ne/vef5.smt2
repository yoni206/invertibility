(set-logic BV)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)
(define-fun min () (_ BitVec 5)
  (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5)))
)
(define-fun max () (_ BitVec 5)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 5)) (t (_ BitVec 5))) Bool (not (= (bvor (bvshl (_ bv7 5) s) t) (_ bv0 5))))

(define-fun l ((x (_ BitVec 5)) (s (_ BitVec 5)) (t (_ BitVec 5))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 5))) (l x s t)))
  (=> (exists ((x (_ BitVec 5))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)