
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
(define-fun inv ((s (_ BitVec 24)) (t (_ BitVec 24))) (_ BitVec 24) (bvneg (bvnot (bvlshr s (bvlshr #b011111111111111111111111 (bvsub #b100000000000000000000000 #b011111111111111111111111))))))
(define-fun l ((x (_ BitVec 24))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 24)) (bvsge s t)) (=> (bvslt s (_ bv0 24)) (bvsge (bvlshr s (_ bv1 24)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
