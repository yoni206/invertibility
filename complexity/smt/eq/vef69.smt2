(set-logic BV)
(declare-fun s () (_ BitVec 69))
(declare-fun t () (_ BitVec 69))

(define-fun udivtotal ((a (_ BitVec 69)) (b (_ BitVec 69))) (_ BitVec 69)
  (ite (= b (_ bv0 69)) (bvnot (_ bv0 69)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 69)) (b (_ BitVec 69))) (_ BitVec 69)
  (ite (= b (_ bv0 69)) a (bvurem a b))
)
(define-fun min () (_ BitVec 69)
  (bvnot (bvlshr (bvnot (_ bv0 69)) (_ bv1 69)))
)
(define-fun max () (_ BitVec 69)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 69)) (t (_ BitVec 69))) Bool (= (bvand (bvshl (bvnot (_ bv0000 69)) s) t) t))

(define-fun l ((x (_ BitVec 69)) (s (_ BitVec 69)) (t (_ BitVec 69))) Bool (= (bvshl x s) t))

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 69))) (l x s t)))
  (=> (exists ((x (_ BitVec 69))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
