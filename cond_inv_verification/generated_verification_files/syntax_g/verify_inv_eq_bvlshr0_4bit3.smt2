
(set-logic QF_BV)

(define-fun min () (_ BitVec 3) (bvnot (bvlshr (bvnot (_ bv0 3)) (_ bv1 3))))

(define-fun max () (_ BitVec 3) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) (bvnot (_ bv0 3)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 3)) (b (_ BitVec 3))) (_ BitVec 3)
  (ite (= b (_ bv0 3)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 3))
(declare-fun t () (_ BitVec 3))
(define-fun inv ((s (_ BitVec 3)) (t (_ BitVec 3))) (_ BitVec 3) (bvshl t s))
(define-fun l ((x (_ BitVec 3))) Bool  (= (bvlshr (inv s t) s) t))
(define-fun SC () Bool (= (bvlshr (bvshl t s) s) t))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
