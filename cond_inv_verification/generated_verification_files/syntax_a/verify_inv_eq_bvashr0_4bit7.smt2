
(set-logic QF_BV)

(define-fun min () (_ BitVec 7) (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7))))

(define-fun max () (_ BitVec 7) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) (bvnot (_ bv0 7)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))
(define-fun inv ((s (_ BitVec 7)) (t (_ BitVec 7))) (_ BitVec 7) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 7))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv7 7)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv7 7)) (or (= t (bvnot (_ bv0 7))) (= t (_ bv0 7))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
