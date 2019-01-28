
(set-logic QF_BV)

(define-fun min () (_ BitVec 32) (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32))))

(define-fun max () (_ BitVec 32) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) (bvnot (_ bv0 32)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 32)) (b (_ BitVec 32))) (_ BitVec 32)
  (ite (= b (_ bv0 32)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(define-fun inv ((s (_ BitVec 32)) (t (_ BitVec 32))) (_ BitVec 32) (bvneg (bvnot (bvlshr s (bvlshr #b01111111111111111111111111111111 (bvsub #b10000000000000000000000000000000 #b01111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 32))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 32)) (bvsge s t)) (=> (bvslt s (_ bv0 32)) (bvsge (bvlshr s (_ bv1 32)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
