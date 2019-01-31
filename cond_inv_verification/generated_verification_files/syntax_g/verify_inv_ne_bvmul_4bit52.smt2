
(set-logic QF_BV)

(define-fun min () (_ BitVec 52) (bvnot (bvlshr (bvnot (_ bv0 52)) (_ bv1 52))))

(define-fun max () (_ BitVec 52) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) (bvnot (_ bv0 52)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 52)) (b (_ BitVec 52))) (_ BitVec 52)
  (ite (= b (_ bv0 52)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 52))
(declare-fun t () (_ BitVec 52))
(define-fun inv ((s (_ BitVec 52)) (t (_ BitVec 52))) (_ BitVec 52) (bvshl #b0111111111111111111111111111111111111111111111111111 t))
(define-fun l ((x (_ BitVec 52))) Bool  (distinct (bvmul (inv s t) s) t))
(define-fun SC () Bool (or (distinct t (_ bv0 52)) (distinct s (_ bv0 52))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
