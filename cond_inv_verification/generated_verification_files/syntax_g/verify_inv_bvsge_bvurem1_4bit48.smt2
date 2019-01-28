
(set-logic QF_BV)

(define-fun min () (_ BitVec 48) (bvnot (bvlshr (bvnot (_ bv0 48)) (_ bv1 48))))

(define-fun max () (_ BitVec 48) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) (bvnot (_ bv0 48)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 48))
(declare-fun t () (_ BitVec 48))
(define-fun inv ((s (_ BitVec 48)) (t (_ BitVec 48))) (_ BitVec 48) (bvsub (bvor s #b100000000000000000000000000000000000000000000000) (bvand t #b011111111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 48))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 48)) (bvsge s t)) (=> (and (bvslt s (_ bv0 48)) (bvsge t (_ bv0 48))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
