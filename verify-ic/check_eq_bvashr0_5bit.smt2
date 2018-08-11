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
(and (=> (bvult s (_ bv5 5)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv5 5)) (or (= t (bvnot (_ bv0 5))) (= t (_ bv0 5)))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 5))) (= (bvashr x s) t)))
  (=> (exists ((x (_ BitVec 5))) (= (bvashr x s) t)) (SC s t))
  )
 )
)
(check-sat)
