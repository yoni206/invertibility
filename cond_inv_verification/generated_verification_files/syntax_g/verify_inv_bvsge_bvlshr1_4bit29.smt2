
(set-logic QF_BV)

(define-fun min () (_ BitVec 29) (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29))))

(define-fun max () (_ BitVec 29) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) (bvnot (_ bv0 29)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 29))
(declare-fun t () (_ BitVec 29))
(define-fun inv ((s (_ BitVec 29)) (t (_ BitVec 29))) (_ BitVec 29) (bvlshr s (bvlshr #b01111111111111111111111111111 (bvsub #b10000000000000000000000000000 #b01111111111111111111111111111))))
(define-fun l ((x (_ BitVec 29))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 29)) (bvsge (bvlshr s (_ bv1 29)) t)) (=> (bvsge s (_ bv0 29)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)