
(set-logic QF_BV)

(define-fun min () (_ BitVec 40) (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40))))

(define-fun max () (_ BitVec 40) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) (bvnot (_ bv0 40)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 40))
(declare-fun t () (_ BitVec 40))
(define-fun inv ((s (_ BitVec 40)) (t (_ BitVec 40))) (_ BitVec 40) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 40))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv40 40)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv40 40)) (or (= t (bvnot (_ bv0 40))) (= t (_ bv0 40))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
