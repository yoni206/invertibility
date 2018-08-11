(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun t () (_ BitVec 37))

(define-fun udivtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) (bvnot (_ bv0 37)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) a (bvurem a b))
)
(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 37)) (t (_ BitVec 37))) Bool
(and (=> (bvult s (_ bv37 37)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv37 37)) (or (= t (bvnot (_ bv0 37))) (= t (_ bv0 37)))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 37))) (= (bvashr x s) t)))
  (=> (exists ((x (_ BitVec 37))) (= (bvashr x s) t)) (SC s t))
  )
 )
)
(check-sat)
