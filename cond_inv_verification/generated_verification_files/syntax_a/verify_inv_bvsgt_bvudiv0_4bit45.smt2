
(set-logic QF_BV)

(define-fun min () (_ BitVec 45) (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45))))

(define-fun max () (_ BitVec 45) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))
(define-fun inv ((s (_ BitVec 45)) (t (_ BitVec 45))) (_ BitVec 45) (bvadd s (bvmul s t)))
(define-fun l ((x (_ BitVec 45))) Bool  (bvsgt (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsgt (udivtotal (bvnot (_ bv0 45)) s) t) (bvsgt (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
