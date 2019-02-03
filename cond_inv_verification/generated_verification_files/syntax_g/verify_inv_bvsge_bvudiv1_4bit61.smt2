
(set-logic QF_BV)

(define-fun min () (_ BitVec 61) (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61))))

(define-fun max () (_ BitVec 61) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) (bvnot (_ bv0 61)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 61))
(declare-fun t () (_ BitVec 61))
(define-fun inv ((s (_ BitVec 61)) (t (_ BitVec 61))) (_ BitVec 61) (bvneg (bvnot (bvlshr s (bvlshr #b0111111111111111111111111111111111111111111111111111111111111 (bvsub #b1000000000000000000000000000000000000000000000000000000000000 #b0111111111111111111111111111111111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 61))) Bool  (bvsge (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 61)) (bvsge s t)) (=> (bvslt s (_ bv0 61)) (bvsge (bvlshr s (_ bv1 61)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)