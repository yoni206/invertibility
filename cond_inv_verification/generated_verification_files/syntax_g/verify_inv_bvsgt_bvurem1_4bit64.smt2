
(set-logic QF_BV)

(define-fun min () (_ BitVec 64) (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64))))

(define-fun max () (_ BitVec 64) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))
(define-fun inv ((s (_ BitVec 64)) (t (_ BitVec 64))) (_ BitVec 64) (bvsub (bvor s #b1000000000000000000000000000000000000000000000000000000000000000) (bvand #b0111111111111111111111111111111111111111111111111111111111111111 (bvsub t #b0111111111111111111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 64))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 64)) (bvsgt s t)) (=> (bvslt s (_ bv0 64)) (bvsgt (bvlshr (bvsub s (_ bv1 64)) (_ bv1 64)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
