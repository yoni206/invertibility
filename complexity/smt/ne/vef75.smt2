(set-logic BV)
(declare-fun s () (_ BitVec 75))
(declare-fun t () (_ BitVec 75))

(define-fun udivtotal ((a (_ BitVec 75)) (b (_ BitVec 75))) (_ BitVec 75)
  (ite (= b (_ bv0 75)) (bvnot (_ bv0 75)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 75)) (b (_ BitVec 75))) (_ BitVec 75)
  (ite (= b (_ bv0 75)) a (bvurem a b))
)
(define-fun min () (_ BitVec 75)
  (bvnot (bvlshr (bvnot (_ bv0 75)) (_ bv1 75)))
)
(define-fun max () (_ BitVec 75)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 75)) (t (_ BitVec 75))) Bool (not (= (bvor (bvshl (_ bv7 75) s) t) (_ bv0 75))))

(define-fun l ((x (_ BitVec 75)) (s (_ BitVec 75)) (t (_ BitVec 75))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 75))) (l x s t)))
  (=> (exists ((x (_ BitVec 75))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
