
(set-logic QF_BV)

(define-fun min () (_ BitVec 15) (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15))))

(define-fun max () (_ BitVec 15) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) (bvnot (_ bv0 15)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 15))
(declare-fun t () (_ BitVec 15))
(define-fun inv ((s (_ BitVec 15)) (t (_ BitVec 15))) (_ BitVec 15) (bvsub (bvor s #b100000000000000) s))
(define-fun l ((x (_ BitVec 15))) Bool  (bvslt (bvashr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 15) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
