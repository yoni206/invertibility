
(set-logic QF_BV)

(define-fun min () (_ BitVec 19) (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19))))

(define-fun max () (_ BitVec 19) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) (bvnot (_ bv0 19)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 19)) (b (_ BitVec 19))) (_ BitVec 19)
  (ite (= b (_ bv0 19)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 19))
(declare-fun t () (_ BitVec 19))
(define-fun inv ((s (_ BitVec 19)) (t (_ BitVec 19))) (_ BitVec 19) (bvneg (bvand (bvor s #b1000000000000000000) (bvnot (bvand s #b1000000000000000000)))))
(define-fun l ((x (_ BitVec 19))) Bool  (bvslt (bvadd (inv s t) s) t))
(define-fun SC () Bool (distinct t min))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
