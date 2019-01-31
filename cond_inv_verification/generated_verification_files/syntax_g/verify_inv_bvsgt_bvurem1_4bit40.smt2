
(set-logic QF_BV)

(define-fun min () (_ BitVec 40) (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40))))

(define-fun max () (_ BitVec 40) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) (bvnot (_ bv0 40)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 40))
(declare-fun t () (_ BitVec 40))
(define-fun inv ((s (_ BitVec 40)) (t (_ BitVec 40))) (_ BitVec 40) (bvsub (bvor s #b1000000000000000000000000000000000000000) (bvand #b0111111111111111111111111111111111111111 (bvsub t #b0111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 40))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 40)) (bvsgt s t)) (=> (bvslt s (_ bv0 40)) (bvsgt (bvlshr (bvsub s (_ bv1 40)) (_ bv1 40)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
