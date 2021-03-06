(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)
(define-fun min () (_ BitVec 5)
  (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5)))
)
(define-fun max () (_ BitVec 5)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 5)) (t (_ BitVec 5))) Bool
(and (=> (bvsge s (_ bv0 5)) (bvsgt s t)) (=> (bvslt s (_ bv0 5)) (bvsgt (bvlshr (bvsub s (_ bv1 5)) (_ bv1 5)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 5))) (bvsgt (uremtotal s x) t)))
  (=> (exists ((x (_ BitVec 5))) (bvsgt (uremtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
