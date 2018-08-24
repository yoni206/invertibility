(set-logic BV)
(declare-fun s () (_ BitVec 86))
(declare-fun t () (_ BitVec 86))

(define-fun udivtotal ((a (_ BitVec 86)) (b (_ BitVec 86))) (_ BitVec 86)
  (ite (= b (_ bv0 86)) (bvnot (_ bv0 86)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 86)) (b (_ BitVec 86))) (_ BitVec 86)
  (ite (= b (_ bv0 86)) a (bvurem a b))
)
(define-fun min () (_ BitVec 86)
  (bvnot (bvlshr (bvnot (_ bv0 86)) (_ bv1 86)))
)
(define-fun max () (_ BitVec 86)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 86)) (t (_ BitVec 86))) Bool (= (bvand (bvshl (bvnot (_ bv0000 86)) s) t) t))

(define-fun l ((x (_ BitVec 86)) (s (_ BitVec 86)) (t (_ BitVec 86))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 86))) (l x s t)))
  (=> (exists ((x (_ BitVec 86))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
