
(set-logic QF_BV)

(define-fun min () (_ BitVec 56) (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56))))

(define-fun max () (_ BitVec 56) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) (bvnot (_ bv0 56)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 56))
(declare-fun t () (_ BitVec 56))
(define-fun inv ((s (_ BitVec 56)) (t (_ BitVec 56))) (_ BitVec 56) (bvshl #b01111111111111111111111111111111111111111111111111111111 t))
(define-fun l ((x (_ BitVec 56))) Bool  (distinct (bvmul (inv s t) s) t))
(define-fun SC () Bool (or (distinct t (_ bv0 56)) (distinct s (_ bv0 56))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
