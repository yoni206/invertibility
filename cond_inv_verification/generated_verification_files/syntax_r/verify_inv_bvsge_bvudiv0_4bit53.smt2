
(set-logic QF_BV)

(define-fun min () (_ BitVec 53) (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53))))

(define-fun max () (_ BitVec 53) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) (bvnot (_ bv0 53)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 53))
(declare-fun t () (_ BitVec 53))
(define-fun inv ((s (_ BitVec 53)) (t (_ BitVec 53))) (_ BitVec 53) (bvor s (bvor t (bvneg (bvnot (bvneg s))))))
(define-fun l ((x (_ BitVec 53))) Bool  (bvsge (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsge (udivtotal (bvnot (_ bv0 53)) s) t) (bvsge (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
