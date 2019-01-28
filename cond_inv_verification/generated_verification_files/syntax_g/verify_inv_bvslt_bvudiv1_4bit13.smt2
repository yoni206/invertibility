
(set-logic QF_BV)

(define-fun min () (_ BitVec 13) (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13))))

(define-fun max () (_ BitVec 13) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) (bvnot (_ bv0 13)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 13))
(declare-fun t () (_ BitVec 13))
(define-fun inv ((s (_ BitVec 13)) (t (_ BitVec 13))) (_ BitVec 13) (bvlshr s (bvlshr #b0111111111111 (bvsub #b1000000000000 #b0111111111111))))
(define-fun l ((x (_ BitVec 13))) Bool  (bvslt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvsge t (_ bv0 13))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
