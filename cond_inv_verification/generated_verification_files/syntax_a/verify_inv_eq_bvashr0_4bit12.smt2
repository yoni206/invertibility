
(set-logic QF_BV)

(define-fun min () (_ BitVec 12) (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12))))

(define-fun max () (_ BitVec 12) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) (bvnot (_ bv0 12)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 12))
(declare-fun t () (_ BitVec 12))
(define-fun inv ((s (_ BitVec 12)) (t (_ BitVec 12))) (_ BitVec 12) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 12))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv12 12)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv12 12)) (or (= t (bvnot (_ bv0 12))) (= t (_ bv0 12))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
