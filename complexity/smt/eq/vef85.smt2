(set-logic BV)
(declare-fun s () (_ BitVec 85))
(declare-fun t () (_ BitVec 85))

(define-fun udivtotal ((a (_ BitVec 85)) (b (_ BitVec 85))) (_ BitVec 85)
  (ite (= b (_ bv0 85)) (bvnot (_ bv0 85)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 85)) (b (_ BitVec 85))) (_ BitVec 85)
  (ite (= b (_ bv0 85)) a (bvurem a b))
)
(define-fun min () (_ BitVec 85)
  (bvnot (bvlshr (bvnot (_ bv0 85)) (_ bv1 85)))
)
(define-fun max () (_ BitVec 85)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 85)) (t (_ BitVec 85))) Bool (= (bvand (bvshl (bvnot (_ bv0000 85)) s) t) t))

(define-fun l ((x (_ BitVec 85)) (s (_ BitVec 85)) (t (_ BitVec 85))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 85))) (l x s t)))
  (=> (exists ((x (_ BitVec 85))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
