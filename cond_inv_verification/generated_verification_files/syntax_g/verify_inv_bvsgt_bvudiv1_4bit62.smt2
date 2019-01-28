
(set-logic QF_BV)

(define-fun min () (_ BitVec 62) (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62))))

(define-fun max () (_ BitVec 62) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) (bvnot (_ bv0 62)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 62))
(declare-fun t () (_ BitVec 62))
(define-fun inv ((s (_ BitVec 62)) (t (_ BitVec 62))) (_ BitVec 62) (bvneg (bvnot (bvlshr s (bvlshr #b01111111111111111111111111111111111111111111111111111111111111 (bvsub #b10000000000000000000000000000000000000000000000000000000000000 #b01111111111111111111111111111111111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 62))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 62)) (bvsgt s t)) (=> (bvslt s (_ bv0 62)) (bvsgt (bvlshr s (_ bv1 62)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
