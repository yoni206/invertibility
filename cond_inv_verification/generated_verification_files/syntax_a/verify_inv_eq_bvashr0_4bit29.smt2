
(set-logic QF_BV)

(define-fun min () (_ BitVec 29) (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29))))

(define-fun max () (_ BitVec 29) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) (bvnot (_ bv0 29)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 29))
(declare-fun t () (_ BitVec 29))
(define-fun inv ((s (_ BitVec 29)) (t (_ BitVec 29))) (_ BitVec 29) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 29))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv29 29)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv29 29)) (or (= t (bvnot (_ bv0 29))) (= t (_ bv0 29))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
