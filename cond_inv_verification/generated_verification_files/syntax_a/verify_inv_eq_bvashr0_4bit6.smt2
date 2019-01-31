
(set-logic QF_BV)

(define-fun min () (_ BitVec 6) (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6))))

(define-fun max () (_ BitVec 6) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) (bvnot (_ bv0 6)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 6)) (b (_ BitVec 6))) (_ BitVec 6)
  (ite (= b (_ bv0 6)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 6))
(declare-fun t () (_ BitVec 6))
(define-fun inv ((s (_ BitVec 6)) (t (_ BitVec 6))) (_ BitVec 6) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 6))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv6 6)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv6 6)) (or (= t (bvnot (_ bv0 6))) (= t (_ bv0 6))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
