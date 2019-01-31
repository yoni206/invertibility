
(set-logic QF_BV)

(define-fun min () (_ BitVec 36) (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36))))

(define-fun max () (_ BitVec 36) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) (bvnot (_ bv0 36)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 36)) (b (_ BitVec 36))) (_ BitVec 36)
  (ite (= b (_ bv0 36)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 36))
(declare-fun t () (_ BitVec 36))
(define-fun inv ((s (_ BitVec 36)) (t (_ BitVec 36))) (_ BitVec 36) (bvneg (bvnot (bvlshr s (bvlshr #b011111111111111111111111111111111111 (bvsub #b100000000000000000000000000000000000 #b011111111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 36))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 36)) (bvsge s t)) (=> (bvslt s (_ bv0 36)) (bvsge (bvlshr s (_ bv1 36)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
