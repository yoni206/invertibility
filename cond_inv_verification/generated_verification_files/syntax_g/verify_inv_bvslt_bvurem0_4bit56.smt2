
(set-logic QF_BV)

(define-fun min () (_ BitVec 56) (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56))))

(define-fun max () (_ BitVec 56) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) (bvnot (_ bv0 56)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 56))
(declare-fun t () (_ BitVec 56))
(define-fun inv ((s (_ BitVec 56)) (t (_ BitVec 56))) (_ BitVec 56) (bvshl #b10000000000000000000000000000000000000000000000000000000 (bvshl t t)))
(define-fun l ((x (_ BitVec 56))) Bool  (bvslt (uremtotal (inv s t) s) t))
(define-fun SC () Bool (bvslt (bvnot t) (bvor (bvneg s) (bvneg t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)