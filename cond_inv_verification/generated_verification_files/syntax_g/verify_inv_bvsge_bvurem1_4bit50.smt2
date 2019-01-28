
(set-logic QF_BV)

(define-fun min () (_ BitVec 50) (bvnot (bvlshr (bvnot (_ bv0 50)) (_ bv1 50))))

(define-fun max () (_ BitVec 50) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) (bvnot (_ bv0 50)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 50))
(declare-fun t () (_ BitVec 50))
(define-fun inv ((s (_ BitVec 50)) (t (_ BitVec 50))) (_ BitVec 50) (bvsub (bvor s #b10000000000000000000000000000000000000000000000000) (bvand t #b01111111111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 50))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 50)) (bvsge s t)) (=> (and (bvslt s (_ bv0 50)) (bvsge t (_ bv0 50))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
