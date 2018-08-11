(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 36))
(declare-fun t () (_ BitVec 36))

(define-fun udivtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) (bvnot (_ bv0 36)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) a (bvurem a b))
)
(define-fun min () (_ BitVec 36)
  (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36)))
)
(define-fun max () (_ BitVec 36)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 36)) (t (_ BitVec 36))) Bool
(and (=> (bvult s (_ bv36 36)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv36 36)) (or (= t (bvnot (_ bv0 36))) (= t (_ bv0 36)))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 36))) (= (bvashr x s) t)))
  (=> (exists ((x (_ BitVec 36))) (= (bvashr x s) t)) (SC s t))
  )
 )
)
(check-sat)
