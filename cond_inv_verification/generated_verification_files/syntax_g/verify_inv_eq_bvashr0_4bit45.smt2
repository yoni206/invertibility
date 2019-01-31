
(set-logic QF_BV)

(define-fun min () (_ BitVec 45) (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45))))

(define-fun max () (_ BitVec 45) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))
(define-fun inv ((s (_ BitVec 45)) (t (_ BitVec 45))) (_ BitVec 45) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 45))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv45 45)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv45 45)) (or (= t (bvnot (_ bv0 45))) (= t (_ bv0 45))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
