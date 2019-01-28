
(set-logic QF_BV)

(define-fun min () (_ BitVec 32) (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32))))

(define-fun max () (_ BitVec 32) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) (bvnot (_ bv0 32)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(define-fun inv ((s (_ BitVec 32)) (t (_ BitVec 32))) (_ BitVec 32) (bvshl #b01111111111111111111111111111111 t))
(define-fun l ((x (_ BitVec 32))) Bool  (distinct (bvshl (inv s t) s) t))
(define-fun SC () Bool (or (distinct t (_ bv0 32)) (bvult s (_ bv32 32))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
