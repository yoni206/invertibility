
(set-logic QF_BV)

(define-fun min () (_ BitVec 42) (bvnot (bvlshr (bvnot (_ bv0 42)) (_ bv1 42))))

(define-fun max () (_ BitVec 42) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) (bvnot (_ bv0 42)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 42))
(declare-fun t () (_ BitVec 42))
(define-fun inv ((s (_ BitVec 42)) (t (_ BitVec 42))) (_ BitVec 42) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 42))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv42 42)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv42 42)) (or (= t (bvnot (_ bv0 42))) (= t (_ bv0 42))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)