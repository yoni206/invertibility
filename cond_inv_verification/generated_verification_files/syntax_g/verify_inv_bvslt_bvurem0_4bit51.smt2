
(set-logic QF_BV)

(define-fun min () (_ BitVec 51) (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51))))

(define-fun max () (_ BitVec 51) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) (bvnot (_ bv0 51)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 51))
(declare-fun t () (_ BitVec 51))
(define-fun inv ((s (_ BitVec 51)) (t (_ BitVec 51))) (_ BitVec 51) (bvshl #b100000000000000000000000000000000000000000000000000 (bvshl t t)))
(define-fun l ((x (_ BitVec 51))) Bool  (bvslt (uremtotal (inv s t) s) t))
(define-fun SC () Bool (bvslt (bvnot t) (bvor (bvneg s) (bvneg t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
