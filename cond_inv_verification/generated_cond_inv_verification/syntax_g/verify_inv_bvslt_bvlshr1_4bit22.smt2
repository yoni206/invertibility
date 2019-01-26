
(set-logic QF_BV)

(define-fun min () (_ BitVec 22) (bvnot (bvlshr (bvnot (_ bv0 22)) (_ bv1 22))))

(define-fun max () (_ BitVec 22) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) (bvnot (_ bv0 22)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 22))
(declare-fun t () (_ BitVec 22))
(define-fun inv ((s (_ BitVec 22)) (t (_ BitVec 22))) (_ BitVec 22) (bvand (bvadd t #b0111111111111111111111) #b1000000000000000000000))
(define-fun l ((x (_ BitVec 22))) Bool  (bvslt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 22) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
