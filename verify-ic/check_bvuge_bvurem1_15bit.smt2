(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 15))
(declare-fun t () (_ BitVec 15))

(define-fun udivtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) (bvnot (_ bv0 15)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) a (bvurem a b))
)
(define-fun min () (_ BitVec 15)
  (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15)))
)
(define-fun max () (_ BitVec 15)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 15)) (t (_ BitVec 15))) Bool
(or (bvuge (bvand (bvsub (bvadd t t) s) s) t) (bvult t s))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 15))) (bvuge (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 15))) (bvuge (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
