
(set-logic QF_BV)

(define-fun min () (_ BitVec 17) (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17))))

(define-fun max () (_ BitVec 17) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))
(define-fun inv ((s (_ BitVec 17)) (t (_ BitVec 17))) (_ BitVec 17) (bvand (bvnot s) #b10000000000000000))
(define-fun l ((x (_ BitVec 17))) Bool  (bvslt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 17) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
