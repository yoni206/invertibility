(set-logic BV)
(declare-fun s () (_ BitVec 76))
(declare-fun t () (_ BitVec 76))

(define-fun udivtotal ((a (_ BitVec 76)) (b (_ BitVec 76))) (_ BitVec 76)
  (ite (= b (_ bv0 76)) (bvnot (_ bv0 76)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 76)) (b (_ BitVec 76))) (_ BitVec 76)
  (ite (= b (_ bv0 76)) a (bvurem a b))
)
(define-fun min () (_ BitVec 76)
  (bvnot (bvlshr (bvnot (_ bv0 76)) (_ bv1 76)))
)
(define-fun max () (_ BitVec 76)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 76)) (t (_ BitVec 76))) Bool (= (bvand (bvshl (bvnot (_ bv0000 76)) s) t) t))

(define-fun l ((x (_ BitVec 76)) (s (_ BitVec 76)) (t (_ BitVec 76))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 76))) (l x s t)))
  (=> (exists ((x (_ BitVec 76))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
