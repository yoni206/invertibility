
(set-logic QF_BV)

(define-fun min () (_ BitVec 26) (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26))))

(define-fun max () (_ BitVec 26) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) (bvnot (_ bv0 26)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 26)) (b (_ BitVec 26))) (_ BitVec 26)
  (ite (= b (_ bv0 26)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 26))
(declare-fun t () (_ BitVec 26))
(define-fun inv ((s (_ BitVec 26)) (t (_ BitVec 26))) (_ BitVec 26) (bvnot (bvor #b01111111111111111111111111 (bvneg s))))
(define-fun l ((x (_ BitVec 26))) Bool  (bvslt (uremtotal (inv s t) s) t))
(define-fun SC () Bool (bvslt (bvnot t) (bvor (bvneg s) (bvneg t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)