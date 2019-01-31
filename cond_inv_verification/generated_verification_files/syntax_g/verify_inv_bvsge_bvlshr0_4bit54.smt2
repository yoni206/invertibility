
(set-logic QF_BV)

(define-fun min () (_ BitVec 54) (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54))))

(define-fun max () (_ BitVec 54) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) (bvnot (_ bv0 54)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 54))
(declare-fun t () (_ BitVec 54))
(define-fun inv ((s (_ BitVec 54)) (t (_ BitVec 54))) (_ BitVec 54) (bvshl t s))
(define-fun l ((x (_ BitVec 54))) Bool  (bvsge (bvlshr (inv s t) s) t))
(define-fun SC () Bool (=> (not (= s (_ bv0 54))) (bvsge (bvlshr (bvnot (_ bv0 54)) s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
