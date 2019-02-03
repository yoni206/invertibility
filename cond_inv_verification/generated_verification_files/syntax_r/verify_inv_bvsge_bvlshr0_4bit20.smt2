
(set-logic QF_BV)

(define-fun min () (_ BitVec 20) (bvnot (bvlshr (bvnot (_ bv0 20)) (_ bv1 20))))

(define-fun max () (_ BitVec 20) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) (bvnot (_ bv0 20)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 20))
(declare-fun t () (_ BitVec 20))
(define-fun inv ((s (_ BitVec 20)) (t (_ BitVec 20))) (_ BitVec 20) (bvor t (bvneg s)))
(define-fun l ((x (_ BitVec 20))) Bool  (bvsge (bvlshr (inv s t) s) t))
(define-fun SC () Bool (=> (not (= s (_ bv0 20))) (bvsge (bvlshr (bvnot (_ bv0 20)) s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)