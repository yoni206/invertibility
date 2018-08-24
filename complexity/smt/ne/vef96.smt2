(set-logic BV)
(declare-fun s () (_ BitVec 96))
(declare-fun t () (_ BitVec 96))

(define-fun udivtotal ((a (_ BitVec 96)) (b (_ BitVec 96))) (_ BitVec 96)
  (ite (= b (_ bv0 96)) (bvnot (_ bv0 96)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 96)) (b (_ BitVec 96))) (_ BitVec 96)
  (ite (= b (_ bv0 96)) a (bvurem a b))
)
(define-fun min () (_ BitVec 96)
  (bvnot (bvlshr (bvnot (_ bv0 96)) (_ bv1 96)))
)
(define-fun max () (_ BitVec 96)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 96)) (t (_ BitVec 96))) Bool (not (= (bvor (bvshl (_ bv7 96) s) t) (_ bv0 96))))

(define-fun l ((x (_ BitVec 96)) (s (_ BitVec 96)) (t (_ BitVec 96))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 96))) (l x s t)))
  (=> (exists ((x (_ BitVec 96))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
