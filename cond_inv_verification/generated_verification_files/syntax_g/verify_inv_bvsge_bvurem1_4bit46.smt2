
(set-logic QF_BV)

(define-fun min () (_ BitVec 46) (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46))))

(define-fun max () (_ BitVec 46) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) (bvnot (_ bv0 46)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 46)) (b (_ BitVec 46))) (_ BitVec 46)
  (ite (= b (_ bv0 46)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 46))
(declare-fun t () (_ BitVec 46))
(define-fun inv ((s (_ BitVec 46)) (t (_ BitVec 46))) (_ BitVec 46) (bvsub (bvor s #b1000000000000000000000000000000000000000000000) (bvand t #b0111111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 46))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 46)) (bvsge s t)) (=> (and (bvslt s (_ bv0 46)) (bvsge t (_ bv0 46))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)