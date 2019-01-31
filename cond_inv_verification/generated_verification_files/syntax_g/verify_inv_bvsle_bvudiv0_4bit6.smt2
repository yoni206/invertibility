
(set-logic QF_BV)

(define-fun min () (_ BitVec 6) (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6))))

(define-fun max () (_ BitVec 6) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) (bvnot (_ bv0 6)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(define-fun inv ((s (_ BitVec 6)) (t (_ BitVec 6))) (_ BitVec 6) t)
(define-fun l ((x (_ BitVec 6))) Bool  (bvsle (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (= (udivtotal (bvmul s t) s) t) (=> (bvsle t (_ bv0 6)) (bvslt (udivtotal min s) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
