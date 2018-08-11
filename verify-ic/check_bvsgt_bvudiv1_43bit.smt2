(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 43))
(declare-fun t () (_ BitVec 43))

(define-fun udivtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) (bvnot (_ bv0 43)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) a (bvurem a b))
)
(define-fun min () (_ BitVec 43)
  (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43)))
)
(define-fun max () (_ BitVec 43)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 43)) (t (_ BitVec 43))) Bool
(and (=> (bvsge s (_ bv0 43)) (bvsgt s t)) (=> (bvslt s (_ bv0 43)) (bvsgt (bvlshr s (_ bv1 43)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 43))) (bvsgt (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 43))) (bvsgt (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
