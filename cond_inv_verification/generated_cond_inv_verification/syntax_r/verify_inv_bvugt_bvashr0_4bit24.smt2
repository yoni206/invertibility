
(set-logic QF_BV)

(define-fun min () (_ BitVec 24) (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24))))

(define-fun max () (_ BitVec 24) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) (bvnot (_ bv0 24)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 24)) (b (_ BitVec 24))) (_ BitVec 24)
  (ite (= b (_ bv0 24)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 24))
(declare-fun t () (_ BitVec 24))
(define-fun inv ((s (_ BitVec 24)) (t (_ BitVec 24))) (_ BitVec 24) (bvor #b011111111111111111111111 #b100000000000000000000000))
(define-fun l ((x (_ BitVec 24))) Bool  (bvugt (bvashr (inv s t) s) t))
(define-fun SC () Bool (bvult t (bvnot (_ bv0 24))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
