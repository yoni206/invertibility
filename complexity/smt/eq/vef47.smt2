(set-logic BV)
(declare-fun s () (_ BitVec 47))
(declare-fun t () (_ BitVec 47))

(define-fun udivtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) (bvnot (_ bv0 47)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) a (bvurem a b))
)
(define-fun min () (_ BitVec 47)
  (bvnot (bvlshr (bvnot (_ bv0 47)) (_ bv1 47)))
)
(define-fun max () (_ BitVec 47)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 47)) (t (_ BitVec 47))) Bool (= (bvand (bvshl (bvnot (_ bv0000 47)) s) t) t))

(define-fun l ((x (_ BitVec 47)) (s (_ BitVec 47)) (t (_ BitVec 47))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 47))) (l x s t)))
  (=> (exists ((x (_ BitVec 47))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
