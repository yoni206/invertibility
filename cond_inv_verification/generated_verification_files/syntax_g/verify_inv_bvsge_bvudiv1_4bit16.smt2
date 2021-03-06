
(set-logic QF_BV)

(define-fun min () (_ BitVec 16) (bvnot (bvlshr (bvnot (_ bv0 16)) (_ bv1 16))))

(define-fun max () (_ BitVec 16) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) (bvnot (_ bv0 16)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))
(define-fun inv ((s (_ BitVec 16)) (t (_ BitVec 16))) (_ BitVec 16) (bvneg (bvnot (bvlshr s (bvlshr #b0111111111111111 (bvsub #b1000000000000000 #b0111111111111111))))))
(define-fun l ((x (_ BitVec 16))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 16)) (bvsge s t)) (=> (bvslt s (_ bv0 16)) (bvsge (bvlshr s (_ bv1 16)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
