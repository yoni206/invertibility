
(set-logic QF_BV)

(define-fun min () (_ BitVec 2) (bvnot (bvlshr (bvnot (_ bv0 2)) (_ bv1 2))))

(define-fun max () (_ BitVec 2) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 2)
  (ite (= b (_ bv0 2)) (bvnot (_ bv0 2)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 2)
  (ite (= b (_ bv0 2)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 2))
(declare-fun t () (_ BitVec 2))
(define-fun inv ((s (_ BitVec 2)) (t (_ BitVec 2))) (_ BitVec 2) (bvshl #b01 s))
(define-fun l ((x (_ BitVec 2))) Bool  (bvsgt (bvlshr (inv s t) s) t))
(define-fun SC () Bool (bvslt t (bvlshr (bvshl max s) s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
