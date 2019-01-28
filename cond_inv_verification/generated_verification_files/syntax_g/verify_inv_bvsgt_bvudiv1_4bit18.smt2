
(set-logic QF_BV)

(define-fun min () (_ BitVec 18) (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18))))

(define-fun max () (_ BitVec 18) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) (bvnot (_ bv0 18)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 18))
(declare-fun t () (_ BitVec 18))
(define-fun inv ((s (_ BitVec 18)) (t (_ BitVec 18))) (_ BitVec 18) (bvneg (bvnot (bvlshr s (bvlshr #b011111111111111111 (bvsub #b100000000000000000 #b011111111111111111))))))
(define-fun l ((x (_ BitVec 18))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 18)) (bvsgt s t)) (=> (bvslt s (_ bv0 18)) (bvsgt (bvlshr s (_ bv1 18)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
