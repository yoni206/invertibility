
(set-logic QF_BV)

(define-fun min () (_ BitVec 25) (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25))))

(define-fun max () (_ BitVec 25) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) (bvnot (_ bv0 25)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 25))
(declare-fun t () (_ BitVec 25))
(define-fun inv ((s (_ BitVec 25)) (t (_ BitVec 25))) (_ BitVec 25) (bvneg (bvnot (bvlshr s (bvlshr #b0111111111111111111111111 (bvsub #b1000000000000000000000000 #b0111111111111111111111111))))))
(define-fun l ((x (_ BitVec 25))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 25)) (bvsge s t)) (=> (bvslt s (_ bv0 25)) (bvsge (bvlshr s (_ bv1 25)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)