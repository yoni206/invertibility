
(set-logic QF_BV)

(define-fun min () (_ BitVec 63) (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63))))

(define-fun max () (_ BitVec 63) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))
(define-fun inv ((s (_ BitVec 63)) (t (_ BitVec 63))) (_ BitVec 63) (bvsub (bvor s #b100000000000000000000000000000000000000000000000000000000000000) (bvand #b011111111111111111111111111111111111111111111111111111111111111 (bvsub t #b011111111111111111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 63))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 63)) (bvsgt s t)) (=> (bvslt s (_ bv0 63)) (bvsgt (bvlshr (bvsub s (_ bv1 63)) (_ bv1 63)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
