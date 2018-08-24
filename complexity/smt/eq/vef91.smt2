(set-logic BV)
(declare-fun s () (_ BitVec 91))
(declare-fun t () (_ BitVec 91))

(define-fun udivtotal ((a (_ BitVec 91)) (b (_ BitVec 91))) (_ BitVec 91)
  (ite (= b (_ bv0 91)) (bvnot (_ bv0 91)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 91)) (b (_ BitVec 91))) (_ BitVec 91)
  (ite (= b (_ bv0 91)) a (bvurem a b))
)
(define-fun min () (_ BitVec 91)
  (bvnot (bvlshr (bvnot (_ bv0 91)) (_ bv1 91)))
)
(define-fun max () (_ BitVec 91)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 91)) (t (_ BitVec 91))) Bool (= (bvand (bvshl (bvnot (_ bv0000 91)) s) t) t))

(define-fun l ((x (_ BitVec 91)) (s (_ BitVec 91)) (t (_ BitVec 91))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 91))) (l x s t)))
  (=> (exists ((x (_ BitVec 91))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
