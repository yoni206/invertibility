(set-logic BV)
(declare-fun s () (_ BitVec 67))
(declare-fun t () (_ BitVec 67))

(define-fun udivtotal ((a (_ BitVec 67)) (b (_ BitVec 67))) (_ BitVec 67)
  (ite (= b (_ bv0 67)) (bvnot (_ bv0 67)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 67)) (b (_ BitVec 67))) (_ BitVec 67)
  (ite (= b (_ bv0 67)) a (bvurem a b))
)
(define-fun min () (_ BitVec 67)
  (bvnot (bvlshr (bvnot (_ bv0 67)) (_ bv1 67)))
)
(define-fun max () (_ BitVec 67)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 67)) (t (_ BitVec 67))) Bool (= (bvand (bvshl (bvnot (_ bv0000 67)) s) t) t))

(define-fun l ((x (_ BitVec 67)) (s (_ BitVec 67)) (t (_ BitVec 67))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 67))) (l x s t)))
  (=> (exists ((x (_ BitVec 67))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
