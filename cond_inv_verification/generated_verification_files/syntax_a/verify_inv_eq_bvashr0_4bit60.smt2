
(set-logic QF_BV)

(define-fun min () (_ BitVec 60) (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60))))

(define-fun max () (_ BitVec 60) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))
(define-fun inv ((s (_ BitVec 60)) (t (_ BitVec 60))) (_ BitVec 60) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 60))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv60 60)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv60 60)) (or (= t (bvnot (_ bv0 60))) (= t (_ bv0 60))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
