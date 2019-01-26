
(set-logic QF_BV)

(define-fun min () (_ BitVec 18) (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18))))

(define-fun max () (_ BitVec 18) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) (bvnot (_ bv0 18)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 18))
(declare-fun t () (_ BitVec 18))
(define-fun inv ((s (_ BitVec 18)) (t (_ BitVec 18))) (_ BitVec 18) (bvand (bvnot s) #b100000000000000000))
(define-fun l ((x (_ BitVec 18))) Bool  (bvslt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 18) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
