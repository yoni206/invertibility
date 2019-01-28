
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
(define-fun inv ((s (_ BitVec 50)) (t (_ BitVec 50))) (_ BitVec 50) t)
(define-fun l ((x (_ BitVec 50))) Bool  (bvsge (uremtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvslt t s) (bvsge (_ bv0 50) s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
