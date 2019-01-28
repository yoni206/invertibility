
(set-logic QF_BV)

(define-fun min () (_ BitVec 38) (bvnot (bvlshr (bvnot (_ bv0 38)) (_ bv1 38))))

(define-fun max () (_ BitVec 38) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) (bvnot (_ bv0 38)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 38)) (b (_ BitVec 38))) (_ BitVec 38)
  (ite (= b (_ bv0 38)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 38))
(declare-fun t () (_ BitVec 38))
(define-fun inv ((s (_ BitVec 38)) (t (_ BitVec 38))) (_ BitVec 38) (bvshl #b10000000000000000000000000000000000000 t))
(define-fun l ((x (_ BitVec 38))) Bool  (distinct (bvlshr (inv s t) s) t))
(define-fun SC () Bool (or (distinct t (_ bv0 38)) (bvult s (_ bv38 38))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
