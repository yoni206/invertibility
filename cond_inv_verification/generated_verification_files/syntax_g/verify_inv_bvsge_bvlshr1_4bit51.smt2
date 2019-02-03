
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
(define-fun inv ((s (_ BitVec 51)) (t (_ BitVec 51))) (_ BitVec 51) (bvlshr s (bvlshr #b011111111111111111111111111111111111111111111111111 (bvsub #b100000000000000000000000000000000000000000000000000 #b011111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 51))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 51)) (bvsge (bvlshr s (_ bv1 51)) t)) (=> (bvsge s (_ bv0 51)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)