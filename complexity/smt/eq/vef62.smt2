(set-logic BV)
(declare-fun s () (_ BitVec 62))
(declare-fun t () (_ BitVec 62))

(define-fun udivtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) (bvnot (_ bv0 62)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) a (bvurem a b))
)
(define-fun min () (_ BitVec 62)
  (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62)))
)
(define-fun max () (_ BitVec 62)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 62)) (t (_ BitVec 62))) Bool (= (bvand (bvshl (bvnot (_ bv0000 62)) s) t) t))

(define-fun l ((x (_ BitVec 62)) (s (_ BitVec 62)) (t (_ BitVec 62))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 62))) (l x s t)))
  (=> (exists ((x (_ BitVec 62))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
