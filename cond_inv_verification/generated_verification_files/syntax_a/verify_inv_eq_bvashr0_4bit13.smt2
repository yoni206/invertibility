
(set-logic QF_BV)

(define-fun min () (_ BitVec 13) (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13))))

(define-fun max () (_ BitVec 13) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) (bvnot (_ bv0 13)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 13))
(declare-fun t () (_ BitVec 13))
(define-fun inv ((s (_ BitVec 13)) (t (_ BitVec 13))) (_ BitVec 13) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 13))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv13 13)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv13 13)) (or (= t (bvnot (_ bv0 13))) (= t (_ bv0 13))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)