(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 25))
(declare-fun t () (_ BitVec 25))

(define-fun udivtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) (bvnot (_ bv0 25)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) a (bvurem a b))
)
(define-fun min () (_ BitVec 25)
  (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25)))
)
(define-fun max () (_ BitVec 25)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 25)) (t (_ BitVec 25))) Bool
(distinct t (bvnot (_ bv0 25)))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 25))) (bvugt (bvadd x s) t)))
  (=> (exists ((x (_ BitVec 25))) (bvugt (bvadd x s) t)) (SC s t))
  )
 )
)
(check-sat)
