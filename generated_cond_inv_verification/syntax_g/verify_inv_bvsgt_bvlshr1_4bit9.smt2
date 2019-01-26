
(set-logic QF_BV)

(define-fun min () (_ BitVec 9) (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9))))

(define-fun max () (_ BitVec 9) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) (bvnot (_ bv0 9)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 9))
(declare-fun t () (_ BitVec 9))
(define-fun inv ((s (_ BitVec 9)) (t (_ BitVec 9))) (_ BitVec 9) (bvlshr s (bvlshr #b011111111 (bvsub #b100000000 #b011111111))))
(define-fun l ((x (_ BitVec 9))) Bool  (bvsgt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 9)) (bvsgt (bvlshr s (_ bv1 9)) t)) (=> (bvsge s (_ bv0 9)) (bvsgt s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
