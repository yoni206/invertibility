
(set-logic QF_BV)

(define-fun min () (_ BitVec 49) (bvnot (bvlshr (bvnot (_ bv0 49)) (_ bv1 49))))

(define-fun max () (_ BitVec 49) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) (bvnot (_ bv0 49)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 49))
(declare-fun t () (_ BitVec 49))
(define-fun inv ((s (_ BitVec 49)) (t (_ BitVec 49))) (_ BitVec 49) (bvsub (bvor s #b1000000000000000000000000000000000000000000000000) (bvand #b0111111111111111111111111111111111111111111111111 (bvsub t #b0111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 49))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 49)) (bvsgt s t)) (=> (bvslt s (_ bv0 49)) (bvsgt (bvlshr (bvsub s (_ bv1 49)) (_ bv1 49)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
