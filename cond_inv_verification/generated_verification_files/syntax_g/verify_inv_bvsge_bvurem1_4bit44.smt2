
(set-logic QF_BV)

(define-fun min () (_ BitVec 44) (bvnot (bvlshr (bvnot (_ bv0 44)) (_ bv1 44))))

(define-fun max () (_ BitVec 44) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) (bvnot (_ bv0 44)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 44)) (b (_ BitVec 44))) (_ BitVec 44)
  (ite (= b (_ bv0 44)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 44))
(declare-fun t () (_ BitVec 44))
(define-fun inv ((s (_ BitVec 44)) (t (_ BitVec 44))) (_ BitVec 44) (bvsub (bvor s #b10000000000000000000000000000000000000000000) (bvand t #b01111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 44))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 44)) (bvsge s t)) (=> (and (bvslt s (_ bv0 44)) (bvsge t (_ bv0 44))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
