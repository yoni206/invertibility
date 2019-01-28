
(set-logic QF_BV)

(define-fun min () (_ BitVec 56) (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56))))

(define-fun max () (_ BitVec 56) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) (bvnot (_ bv0 56)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 56))
(declare-fun t () (_ BitVec 56))
(define-fun inv ((s (_ BitVec 56)) (t (_ BitVec 56))) (_ BitVec 56) (bvsub (bvor s #b10000000000000000000000000000000000000000000000000000000) (bvand t #b01111111111111111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 56))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 56)) (bvsge s t)) (=> (and (bvslt s (_ bv0 56)) (bvsge t (_ bv0 56))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
