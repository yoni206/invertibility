
(set-logic QF_BV)

(define-fun min () (_ BitVec 9) (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9))))

(define-fun max () (_ BitVec 9) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) (bvnot (_ bv0 9)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 9))
(declare-fun t () (_ BitVec 9))
(define-fun inv ((s (_ BitVec 9)) (t (_ BitVec 9))) (_ BitVec 9) (bvor (bvlshr #b100000000 (bvand (bvlshr #b011111111 s) s)) #b011111111))
(define-fun l ((x (_ BitVec 9))) Bool  (bvsge (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsge (udivtotal (bvnot (_ bv0 9)) s) t) (bvsge (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
