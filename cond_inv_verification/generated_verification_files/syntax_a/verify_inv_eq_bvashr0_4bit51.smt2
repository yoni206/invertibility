
(set-logic QF_BV)

(define-fun min () (_ BitVec 51) (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51))))

(define-fun max () (_ BitVec 51) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) (bvnot (_ bv0 51)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 51)) (b (_ BitVec 51))) (_ BitVec 51)
  (ite (= b (_ bv0 51)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 51))
(declare-fun t () (_ BitVec 51))
(define-fun inv ((s (_ BitVec 51)) (t (_ BitVec 51))) (_ BitVec 51) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 51))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv51 51)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv51 51)) (or (= t (bvnot (_ bv0 51))) (= t (_ bv0 51))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
