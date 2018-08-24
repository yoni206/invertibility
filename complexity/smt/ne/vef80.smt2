(set-logic BV)
(declare-fun s () (_ BitVec 80))
(declare-fun t () (_ BitVec 80))

(define-fun udivtotal ((a (_ BitVec 80)) (b (_ BitVec 80))) (_ BitVec 80)
  (ite (= b (_ bv0 80)) (bvnot (_ bv0 80)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 80)) (b (_ BitVec 80))) (_ BitVec 80)
  (ite (= b (_ bv0 80)) a (bvurem a b))
)
(define-fun min () (_ BitVec 80)
  (bvnot (bvlshr (bvnot (_ bv0 80)) (_ bv1 80)))
)
(define-fun max () (_ BitVec 80)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 80)) (t (_ BitVec 80))) Bool (not (= (bvor (bvshl (_ bv7 80) s) t) (_ bv0 80))))

(define-fun l ((x (_ BitVec 80)) (s (_ BitVec 80)) (t (_ BitVec 80))) Bool (distinct (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 80))) (l x s t)))
  (=> (exists ((x (_ BitVec 80))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
