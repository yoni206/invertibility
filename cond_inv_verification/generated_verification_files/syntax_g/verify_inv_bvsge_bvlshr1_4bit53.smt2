
(set-logic QF_BV)

(define-fun min () (_ BitVec 53) (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53))))

(define-fun max () (_ BitVec 53) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) (bvnot (_ bv0 53)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 53))
(declare-fun t () (_ BitVec 53))
(define-fun inv ((s (_ BitVec 53)) (t (_ BitVec 53))) (_ BitVec 53) (bvlshr s (bvlshr #b01111111111111111111111111111111111111111111111111111 (bvsub #b10000000000000000000000000000000000000000000000000000 #b01111111111111111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 53))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 53)) (bvsge (bvlshr s (_ bv1 53)) t)) (=> (bvsge s (_ bv0 53)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
