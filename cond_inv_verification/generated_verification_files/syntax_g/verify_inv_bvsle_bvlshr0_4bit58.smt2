
(set-logic QF_BV)

(define-fun min () (_ BitVec 58) (bvnot (bvlshr (bvnot (_ bv0 58)) (_ bv1 58))))

(define-fun max () (_ BitVec 58) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) (bvnot (_ bv0 58)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 58))
(declare-fun t () (_ BitVec 58))
(define-fun inv ((s (_ BitVec 58)) (t (_ BitVec 58))) (_ BitVec 58) t)
(define-fun l ((x (_ BitVec 58))) Bool  (bvsle (bvlshr (inv s t) s) t))
(define-fun SC () Bool (bvsge t (bvlshr t s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
