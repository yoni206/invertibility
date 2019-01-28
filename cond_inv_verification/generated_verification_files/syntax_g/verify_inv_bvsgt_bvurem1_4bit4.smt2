
(set-logic QF_BV)

(define-fun min () (_ BitVec 4) (bvnot (bvlshr (bvnot (_ bv0 4)) (_ bv1 4))))

(define-fun max () (_ BitVec 4) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) (bvnot (_ bv0 4)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(define-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4) (bvsub (bvor s #b1000) (bvand #b0111 (bvsub t #b0111))))
(define-fun l ((x (_ BitVec 4))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 4)) (bvsgt s t)) (=> (bvslt s (_ bv0 4)) (bvsgt (bvlshr (bvsub s (_ bv1 4)) (_ bv1 4)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
