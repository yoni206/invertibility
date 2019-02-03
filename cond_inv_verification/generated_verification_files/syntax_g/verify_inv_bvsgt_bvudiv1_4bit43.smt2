
(set-logic QF_BV)

(define-fun min () (_ BitVec 43) (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43))))

(define-fun max () (_ BitVec 43) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) (bvnot (_ bv0 43)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 43))
(declare-fun t () (_ BitVec 43))
(define-fun inv ((s (_ BitVec 43)) (t (_ BitVec 43))) (_ BitVec 43) (bvneg (bvnot (bvlshr s (bvlshr #b0111111111111111111111111111111111111111111 (bvsub #b1000000000000000000000000000000000000000000 #b0111111111111111111111111111111111111111111))))))
(define-fun l ((x (_ BitVec 43))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 43)) (bvsgt s t)) (=> (bvslt s (_ bv0 43)) (bvsgt (bvlshr s (_ bv1 43)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)