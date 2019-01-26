
(set-logic QF_BV)

(define-fun min () (_ BitVec 10) (bvnot (bvlshr (bvnot (_ bv0 10)) (_ bv1 10))))

(define-fun max () (_ BitVec 10) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) (bvnot (_ bv0 10)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 10)) (b (_ BitVec 10))) (_ BitVec 10)
  (ite (= b (_ bv0 10)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 10))
(declare-fun t () (_ BitVec 10))
(define-fun inv ((s (_ BitVec 10)) (t (_ BitVec 10))) (_ BitVec 10) (bvsub (bvor s #b1000000000) (bvand #b0111111111 t)))
(define-fun l ((x (_ BitVec 10))) Bool  (bvsge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 10)) (bvsge s t)) (=> (and (bvslt s (_ bv0 10)) (bvsge t (_ bv0 10))) (bvugt (bvsub s t) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
