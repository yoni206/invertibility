
(set-logic QF_BV)

(define-fun min () (_ BitVec 14) (bvnot (bvlshr (bvnot (_ bv0 14)) (_ bv1 14))))

(define-fun max () (_ BitVec 14) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) (bvnot (_ bv0 14)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 14))
(declare-fun t () (_ BitVec 14))
(define-fun inv ((s (_ BitVec 14)) (t (_ BitVec 14))) (_ BitVec 14) (bvneg (bvnot (bvlshr s (bvlshr #b01111111111111 (bvsub #b10000000000000 #b01111111111111))))))
(define-fun l ((x (_ BitVec 14))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 14)) (bvsge s t)) (=> (bvslt s (_ bv0 14)) (bvsge (bvlshr s (_ bv1 14)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
