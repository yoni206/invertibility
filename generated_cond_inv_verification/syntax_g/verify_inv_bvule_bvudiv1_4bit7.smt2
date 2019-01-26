
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
(define-fun inv ((s (_ BitVec 7)) (t (_ BitVec 7))) (_ BitVec 7) (bvnot #b0000000))
(define-fun l ((x (_ BitVec 7))) Bool  (bvule (udivtotal s (inv s t)) t))
(define-fun SC () Bool (bvult (_ bv0 7) (bvor (bvnot s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
