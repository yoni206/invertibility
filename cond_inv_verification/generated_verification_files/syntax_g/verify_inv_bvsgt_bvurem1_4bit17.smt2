
(set-logic QF_BV)

(define-fun min () (_ BitVec 17) (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17))))

(define-fun max () (_ BitVec 17) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))
(define-fun inv ((s (_ BitVec 17)) (t (_ BitVec 17))) (_ BitVec 17) (bvsub (bvor s #b10000000000000000) (bvand #b01111111111111111 (bvsub t #b01111111111111111))))
(define-fun l ((x (_ BitVec 17))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 17)) (bvsgt s t)) (=> (bvslt s (_ bv0 17)) (bvsgt (bvlshr (bvsub s (_ bv1 17)) (_ bv1 17)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)