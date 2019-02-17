
(set-logic QF_BV)

(define-fun min () (_ BitVec 64) (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64))))

(define-fun max () (_ BitVec 64) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))
(define-fun inv ((s (_ BitVec 64)) (t (_ BitVec 64))) (_ BitVec 64) (bvor #b0111111111111111111111111111111111111111111111111111111111111111 (bvneg s)))
(define-fun l ((x (_ BitVec 64))) Bool  (bvsgt (bvlshr (inv s t) s) t))
(define-fun SC () Bool (bvslt t (bvlshr (bvshl max s) s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
