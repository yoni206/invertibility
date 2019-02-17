
(set-logic QF_BV)

(define-fun min () (_ BitVec 1) (bvnot (bvlshr (bvnot (_ bv0 1)) (_ bv1 1))))

(define-fun max () (_ BitVec 1) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
  (ite (= b (_ bv0 1)) (bvnot (_ bv0 1)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
  (ite (= b (_ bv0 1)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 1))
(declare-fun t () (_ BitVec 1))
(define-fun inv ((s (_ BitVec 1)) (t (_ BitVec 1))) (_ BitVec 1) (bvnot t))
(define-fun l ((x (_ BitVec 1))) Bool  (distinct (bvor (inv s t) s) t))
(define-fun SC () Bool (or (distinct s (bvnot (_ bv0 1))) (distinct t (bvnot (_ bv0 1)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
