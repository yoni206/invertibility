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
(and (=> (bvult s (_ bv35 35)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv35 35)) (or (= t (bvnot (_ bv0 35))) (= t (_ bv0 35)))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (= (bvashr x s) t)))
  (=> (exists ((x (_ BitVec 35))) (= (bvashr x s) t)) (SC s t))
  )
 )
)
(check-sat)
