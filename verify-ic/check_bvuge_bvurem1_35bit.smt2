(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)
(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 35)) (t (_ BitVec 35))) Bool
(or (bvuge (bvand (bvsub (bvadd t t) s) s) t) (bvult t s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (bvuge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 35))) (bvuge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
