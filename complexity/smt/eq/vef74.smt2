(set-logic BV)
(declare-fun s () (_ BitVec 74))
(declare-fun t () (_ BitVec 74))

(define-fun udivtotal ((a (_ BitVec 74)) (b (_ BitVec 74))) (_ BitVec 74)
  (ite (= b (_ bv0 74)) (bvnot (_ bv0 74)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 74)) (b (_ BitVec 74))) (_ BitVec 74)
  (ite (= b (_ bv0 74)) a (bvurem a b))
)
(define-fun min () (_ BitVec 74)
  (bvnot (bvlshr (bvnot (_ bv0 74)) (_ bv1 74)))
)
(define-fun max () (_ BitVec 74)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 74)) (t (_ BitVec 74))) Bool (= (bvand (bvshl (bvnot (_ bv0000 74)) s) t) t))

(define-fun l ((x (_ BitVec 74)) (s (_ BitVec 74)) (t (_ BitVec 74))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 74))) (l x s t)))
  (=> (exists ((x (_ BitVec 74))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
