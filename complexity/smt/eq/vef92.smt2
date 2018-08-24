(set-logic BV)
(declare-fun s () (_ BitVec 92))
(declare-fun t () (_ BitVec 92))

(define-fun udivtotal ((a (_ BitVec 92)) (b (_ BitVec 92))) (_ BitVec 92)
  (ite (= b (_ bv0 92)) (bvnot (_ bv0 92)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 92)) (b (_ BitVec 92))) (_ BitVec 92)
  (ite (= b (_ bv0 92)) a (bvurem a b))
)
(define-fun min () (_ BitVec 92)
  (bvnot (bvlshr (bvnot (_ bv0 92)) (_ bv1 92)))
)
(define-fun max () (_ BitVec 92)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 92)) (t (_ BitVec 92))) Bool (= (bvand (bvshl (bvnot (_ bv0000 92)) s) t) t))

(define-fun l ((x (_ BitVec 92)) (s (_ BitVec 92)) (t (_ BitVec 92))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 92))) (l x s t)))
  (=> (exists ((x (_ BitVec 92))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
