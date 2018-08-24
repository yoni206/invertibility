(set-logic BV)
(declare-fun s () (_ BitVec 79))
(declare-fun t () (_ BitVec 79))

(define-fun udivtotal ((a (_ BitVec 79)) (b (_ BitVec 79))) (_ BitVec 79)
  (ite (= b (_ bv0 79)) (bvnot (_ bv0 79)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 79)) (b (_ BitVec 79))) (_ BitVec 79)
  (ite (= b (_ bv0 79)) a (bvurem a b))
)
(define-fun min () (_ BitVec 79)
  (bvnot (bvlshr (bvnot (_ bv0 79)) (_ bv1 79)))
)
(define-fun max () (_ BitVec 79)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 79)) (t (_ BitVec 79))) Bool (not (= (bvor (bvshl (_ bv7 79) s) t) (_ bv0 79))))

(define-fun l ((x (_ BitVec 79)) (s (_ BitVec 79)) (t (_ BitVec 79))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 79))) (l x s t)))
  (=> (exists ((x (_ BitVec 79))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
