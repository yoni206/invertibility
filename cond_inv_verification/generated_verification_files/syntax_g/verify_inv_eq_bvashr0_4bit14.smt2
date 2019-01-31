
(set-logic QF_BV)

(define-fun min () (_ BitVec 14) (bvnot (bvlshr (bvnot (_ bv0 14)) (_ bv1 14))))

(define-fun max () (_ BitVec 14) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) (bvnot (_ bv0 14)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 14)) (b (_ BitVec 14))) (_ BitVec 14)
  (ite (= b (_ bv0 14)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 14))
(declare-fun t () (_ BitVec 14))
(define-fun inv ((s (_ BitVec 14)) (t (_ BitVec 14))) (_ BitVec 14) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 14))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv14 14)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv14 14)) (or (= t (bvnot (_ bv0 14))) (= t (_ bv0 14))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
