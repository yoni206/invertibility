(set-logic BV)
(declare-fun s () (_ BitVec 59))
(declare-fun t () (_ BitVec 59))

(define-fun udivtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) (bvnot (_ bv0 59)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) a (bvurem a b))
)
(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 59)) (t (_ BitVec 59))) Bool (= (bvand (bvshl (bvnot (_ bv0000 59)) s) t) t))

(define-fun l ((x (_ BitVec 59)) (s (_ BitVec 59)) (t (_ BitVec 59))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 59))) (l x s t)))
  (=> (exists ((x (_ BitVec 59))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)