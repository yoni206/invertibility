(set-logic BV)
(declare-fun s () (_ BitVec 30))
(declare-fun t () (_ BitVec 30))

(define-fun udivtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) (bvnot (_ bv0 30)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) a (bvurem a b))
)
(define-fun min () (_ BitVec 30)
  (bvnot (bvlshr (bvnot (_ bv0 30)) (_ bv1 30)))
)
(define-fun max () (_ BitVec 30)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 30)) (t (_ BitVec 30))) Bool (= (bvand (bvshl (bvnot (_ bv0000 30)) s) t) t))

(define-fun l ((x (_ BitVec 30)) (s (_ BitVec 30)) (t (_ BitVec 30))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 30))) (l x s t)))
  (=> (exists ((x (_ BitVec 30))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)