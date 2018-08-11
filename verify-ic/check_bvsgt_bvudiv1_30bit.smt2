(set-logic BV)
(set-option :produce-models true)
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

(define-fun SC ((s (_ BitVec 30)) (t (_ BitVec 30))) Bool
(and (=> (bvsge s (_ bv0 30)) (bvsgt s t)) (=> (bvslt s (_ bv0 30)) (bvsgt (bvlshr s (_ bv1 30)) t)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 30))) (bvsgt (udivtotal s x) t)))
  (=> (exists ((x (_ BitVec 30))) (bvsgt (udivtotal s x) t)) (SC s t))
  )
 )
)
(check-sat)
