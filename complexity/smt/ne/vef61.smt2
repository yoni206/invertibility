(set-logic BV)
(declare-fun s () (_ BitVec 61))
(declare-fun t () (_ BitVec 61))

(define-fun udivtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) (bvnot (_ bv0 61)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) a (bvurem a b))
)
(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 61)) (t (_ BitVec 61))) Bool (not (= (bvor (bvshl (_ bv7 61) s) t) (_ bv0 61))))

(define-fun l ((x (_ BitVec 61)) (s (_ BitVec 61)) (t (_ BitVec 61))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 61))) (l x s t)))
  (=> (exists ((x (_ BitVec 61))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
