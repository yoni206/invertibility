
(set-logic QF_BV)

(define-fun min () (_ BitVec 16) (bvnot (bvlshr (bvnot (_ bv0 16)) (_ bv1 16))))

(define-fun max () (_ BitVec 16) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) (bvnot (_ bv0 16)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 16)) (b (_ BitVec 16))) (_ BitVec 16)
  (ite (= b (_ bv0 16)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 16))
(declare-fun t () (_ BitVec 16))
(define-fun inv ((s (_ BitVec 16)) (t (_ BitVec 16))) (_ BitVec 16) #b1000000000000000)
(define-fun l ((x (_ BitVec 16))) Bool  (bvslt (bvand (inv s t) s) t))
(define-fun SC () Bool (bvslt (bvand (bvnot (bvneg t)) s) t))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
