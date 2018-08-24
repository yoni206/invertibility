(set-logic BV)
(declare-fun s () (_ BitVec 82))
(declare-fun t () (_ BitVec 82))

(define-fun udivtotal ((a (_ BitVec 82)) (b (_ BitVec 82))) (_ BitVec 82)
  (ite (= b (_ bv0 82)) (bvnot (_ bv0 82)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 82)) (b (_ BitVec 82))) (_ BitVec 82)
  (ite (= b (_ bv0 82)) a (bvurem a b))
)
(define-fun min () (_ BitVec 82)
  (bvnot (bvlshr (bvnot (_ bv0 82)) (_ bv1 82)))
)
(define-fun max () (_ BitVec 82)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 82)) (t (_ BitVec 82))) Bool (not (= (bvor (bvshl (_ bv7 82) s) t) (_ bv0 82))))

(define-fun l ((x (_ BitVec 82)) (s (_ BitVec 82)) (t (_ BitVec 82))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 82))) (l x s t)))
  (=> (exists ((x (_ BitVec 82))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
