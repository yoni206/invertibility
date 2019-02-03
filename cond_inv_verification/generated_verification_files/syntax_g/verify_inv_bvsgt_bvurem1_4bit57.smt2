
(set-logic QF_BV)

(define-fun min () (_ BitVec 57) (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57))))

(define-fun max () (_ BitVec 57) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) (bvnot (_ bv0 57)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 57))
(declare-fun t () (_ BitVec 57))
(define-fun inv ((s (_ BitVec 57)) (t (_ BitVec 57))) (_ BitVec 57) (bvsub (bvor s #b100000000000000000000000000000000000000000000000000000000) (bvand #b011111111111111111111111111111111111111111111111111111111 (bvsub t #b011111111111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 57))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 57)) (bvsgt s t)) (=> (bvslt s (_ bv0 57)) (bvsgt (bvlshr (bvsub s (_ bv1 57)) (_ bv1 57)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)