(set-logic BV)
(declare-fun s () (_ BitVec 97))
(declare-fun t () (_ BitVec 97))

(define-fun udivtotal ((a (_ BitVec 97)) (b (_ BitVec 97))) (_ BitVec 97)
  (ite (= b (_ bv0 97)) (bvnot (_ bv0 97)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 97)) (b (_ BitVec 97))) (_ BitVec 97)
  (ite (= b (_ bv0 97)) a (bvurem a b))
)
(define-fun min () (_ BitVec 97)
  (bvnot (bvlshr (bvnot (_ bv0 97)) (_ bv1 97)))
)
(define-fun max () (_ BitVec 97)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 97)) (t (_ BitVec 97))) Bool (= (bvand (bvshl (bvnot (_ bv0000 97)) s) t) t))

(define-fun l ((x (_ BitVec 97)) (s (_ BitVec 97)) (t (_ BitVec 97))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 97))) (l x s t)))
  (=> (exists ((x (_ BitVec 97))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
