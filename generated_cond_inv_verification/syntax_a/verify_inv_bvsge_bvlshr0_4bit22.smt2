
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
(define-fun inv ((s (_ BitVec 22)) (t (_ BitVec 22))) (_ BitVec 22) (bvadd (bvmul s t) #b0111111111111111111111))
(define-fun l ((x (_ BitVec 22))) Bool  (bvsge (bvlshr (inv s t) s) t))
(define-fun SC () Bool (=> (not (= s (_ bv0 22))) (bvsge (bvlshr (bvnot (_ bv0 22)) s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
