
(set-logic QF_BV)

(define-fun min () (_ BitVec 4) (bvnot (bvlshr (bvnot (_ bv0 4)) (_ bv1 4))))

(define-fun max () (_ BitVec 4) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) (bvnot (_ bv0 4)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 4)) (b (_ BitVec 4))) (_ BitVec 4)
  (ite (= b (_ bv0 4)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(define-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4) (bvsub (bvmul s t) s))
(define-fun l ((x (_ BitVec 4))) Bool  (bvslt (udivtotal (inv s t) s) t))
(define-fun SC () Bool (=> (bvsle t (_ bv0 4)) (bvslt (udivtotal min s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
