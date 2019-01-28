
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
(define-fun inv ((s (_ BitVec 48)) (t (_ BitVec 48))) (_ BitVec 48) (bvnot (bvshl s (bvor s (bvadd s s)))))
(define-fun l ((x (_ BitVec 48))) Bool  (bvsge (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsge (udivtotal (bvnot (_ bv0 48)) s) t) (bvsge (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
