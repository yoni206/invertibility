
(set-logic QF_BV)

(define-fun min () (_ BitVec 47) (bvnot (bvlshr (bvnot (_ bv0 47)) (_ bv1 47))))

(define-fun max () (_ BitVec 47) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) (bvnot (_ bv0 47)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 47))
(declare-fun t () (_ BitVec 47))
(define-fun inv ((s (_ BitVec 47)) (t (_ BitVec 47))) (_ BitVec 47) (bvnot (bvshl s (bvor s (bvadd s s)))))
(define-fun l ((x (_ BitVec 47))) Bool  (bvsgt (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsgt (udivtotal (bvnot (_ bv0 47)) s) t) (bvsgt (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
