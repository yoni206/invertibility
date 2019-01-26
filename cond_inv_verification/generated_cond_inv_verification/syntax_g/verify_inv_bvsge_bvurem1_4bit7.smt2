
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
(define-fun inv ((s (_ BitVec 7)) (t (_ BitVec 7))) (_ BitVec 7) (bvsub (bvor s #b1000000) (bvand #b0111111 t)))
(define-fun l ((x (_ BitVec 7))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 7)) (bvsge s t)) (=> (and (bvslt s (_ bv0 7)) (bvsge t (_ bv0 7))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
