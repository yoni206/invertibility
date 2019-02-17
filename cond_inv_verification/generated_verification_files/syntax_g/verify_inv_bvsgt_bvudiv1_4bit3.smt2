
(set-logic QF_BV)

(define-fun min () (_ BitVec 3) (bvnot (bvlshr (bvnot (_ bv0 3)) (_ bv1 3))))

(define-fun max () (_ BitVec 3) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) (bvnot (_ bv0 3)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(define-fun inv ((s (_ BitVec 3)) (t (_ BitVec 3))) (_ BitVec 3) (bvneg (bvnot (bvlshr s (bvlshr #b011 (bvsub #b100 #b011))))))
(define-fun l ((x (_ BitVec 3))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 3)) (bvsgt s t)) (=> (bvslt s (_ bv0 3)) (bvsgt (bvlshr s (_ bv1 3)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
