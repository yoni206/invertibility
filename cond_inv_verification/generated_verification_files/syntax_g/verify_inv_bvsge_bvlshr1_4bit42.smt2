
(set-logic QF_BV)

(define-fun min () (_ BitVec 42) (bvnot (bvlshr (bvnot (_ bv0 42)) (_ bv1 42))))

(define-fun max () (_ BitVec 42) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) (bvnot (_ bv0 42)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 42))
(declare-fun t () (_ BitVec 42))
(define-fun inv ((s (_ BitVec 42)) (t (_ BitVec 42))) (_ BitVec 42) (bvlshr s (bvlshr #b011111111111111111111111111111111111111111 (bvsub #b100000000000000000000000000000000000000000 #b011111111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 42))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 42)) (bvsge (bvlshr s (_ bv1 42)) t)) (=> (bvsge s (_ bv0 42)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
