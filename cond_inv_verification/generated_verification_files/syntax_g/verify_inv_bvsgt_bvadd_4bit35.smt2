
(set-logic QF_BV)

(define-fun min () (_ BitVec 35) (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35))))

(define-fun max () (_ BitVec 35) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))
(define-fun inv ((s (_ BitVec 35)) (t (_ BitVec 35))) (_ BitVec 35) (bvsub #b01111111111111111111111111111111111 s))
(define-fun l ((x (_ BitVec 35))) Bool  (bvsgt (bvadd (inv s t) s) t))
(define-fun SC () Bool (distinct t max))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
