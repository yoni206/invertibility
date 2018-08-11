(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 65))
(declare-fun t () (_ BitVec 65))

(define-fun udivtotal ((a (_ BitVec 65)) (b (_ BitVec 65))) (_ BitVec 65)
  (ite (= b (_ bv0 65)) (bvnot (_ bv0 65)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 65)) (b (_ BitVec 65))) (_ BitVec 65)
  (ite (= b (_ bv0 65)) a (bvurem a b))
)
(define-fun min () (_ BitVec 65)
  (bvnot (bvlshr (bvnot (_ bv0 65)) (_ bv1 65)))
)
(define-fun max () (_ BitVec 65)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 65)) (t (_ BitVec 65))) Bool
(and (=> (bvsge s (_ bv0 65)) (bvsgt s t)) (=> (bvslt s (_ bv0 65)) (bvsgt (bvlshr s (_ bv1 65)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 65))) (bvsgt (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 65))) (bvsgt (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
