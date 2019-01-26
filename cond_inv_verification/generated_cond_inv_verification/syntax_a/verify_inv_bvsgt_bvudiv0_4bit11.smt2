
(set-logic QF_BV)

(define-fun min () (_ BitVec 11) (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11))))

(define-fun max () (_ BitVec 11) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) (bvnot (_ bv0 11)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 11))
(declare-fun t () (_ BitVec 11))
(define-fun inv ((s (_ BitVec 11)) (t (_ BitVec 11))) (_ BitVec 11) (bvadd (bvmul t s) s))
(define-fun l ((x (_ BitVec 11))) Bool  (bvsgt (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsgt (udivtotal (bvnot (_ bv0 11)) s) t) (bvsgt (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
