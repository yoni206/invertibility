
(set-logic QF_BV)

(define-fun min () (_ BitVec 45) (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45))))

(define-fun max () (_ BitVec 45) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))
(define-fun inv ((s (_ BitVec 45)) (t (_ BitVec 45))) (_ BitVec 45) (bvlshr s (bvlshr #b011111111111111111111111111111111111111111111 (bvsub #b100000000000000000000000000000000000000000000 #b011111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 45))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 45)) (bvsge (bvlshr s (_ bv1 45)) t)) (=> (bvsge s (_ bv0 45)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
