
(set-logic QF_BV)

(define-fun min () (_ BitVec 55) (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55))))

(define-fun max () (_ BitVec 55) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) (bvnot (_ bv0 55)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 55))
(declare-fun t () (_ BitVec 55))
(define-fun inv ((s (_ BitVec 55)) (t (_ BitVec 55))) (_ BitVec 55) (bvneg (bvnot (bvlshr s (bvlshr #b0111111111111111111111111111111111111111111111111111111 (bvsub #b1000000000000000000000000000000000000000000000000000000 #b0111111111111111111111111111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 55))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 55)) (bvsgt s t)) (=> (bvslt s (_ bv0 55)) (bvsgt (bvlshr s (_ bv1 55)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
