
(set-logic QF_BV)

(define-fun min () (_ BitVec 54) (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54))))

(define-fun max () (_ BitVec 54) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) (bvnot (_ bv0 54)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 54))
(declare-fun t () (_ BitVec 54))
(define-fun inv ((s (_ BitVec 54)) (t (_ BitVec 54))) (_ BitVec 54) (bvlshr s (bvlshr #b011111111111111111111111111111111111111111111111111111 (bvsub #b100000000000000000000000000000000000000000000000000000 #b011111111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 54))) Bool  (bvsgt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 54)) (bvsgt (bvlshr s (_ bv1 54)) t)) (=> (bvsge s (_ bv0 54)) (bvsgt s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
