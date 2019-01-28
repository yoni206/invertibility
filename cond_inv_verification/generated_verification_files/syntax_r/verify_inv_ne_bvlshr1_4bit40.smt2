
(set-logic QF_BV)

(define-fun min () (_ BitVec 40) (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40))))

(define-fun max () (_ BitVec 40) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) (bvnot (_ bv0 40)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 40)) (b (_ BitVec 40))) (_ BitVec 40)
  (ite (= b (_ bv0 40)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 40))
(declare-fun t () (_ BitVec 40))
(define-fun inv ((s (_ BitVec 40)) (t (_ BitVec 40))) (_ BitVec 40) (bvneg t))
(define-fun l ((x (_ BitVec 40))) Bool  (distinct (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (distinct s (_ bv0 40)) (distinct t (_ bv0 40))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
