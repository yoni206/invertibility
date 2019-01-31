
(set-logic QF_BV)

(define-fun min () (_ BitVec 18) (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18))))

(define-fun max () (_ BitVec 18) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) (bvnot (_ bv0 18)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 18)) (b (_ BitVec 18))) (_ BitVec 18)
  (ite (= b (_ bv0 18)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 18))
(declare-fun t () (_ BitVec 18))
(define-fun inv ((s (_ BitVec 18)) (t (_ BitVec 18))) (_ BitVec 18) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 18))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv18 18)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv18 18)) (or (= t (bvnot (_ bv0 18))) (= t (_ bv0 18))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
