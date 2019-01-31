
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
(define-fun inv ((s (_ BitVec 14)) (t (_ BitVec 14))) (_ BitVec 14) (bvsub (bvor s #b10000000000000) (bvand #b01111111111111 (bvsub t #b01111111111111))))
(define-fun l ((x (_ BitVec 14))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 14)) (bvsgt s t)) (=> (bvslt s (_ bv0 14)) (bvsgt (bvlshr (bvsub s (_ bv1 14)) (_ bv1 14)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
