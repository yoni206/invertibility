
(set-logic QF_BV)

(define-fun min () (_ BitVec 17) (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17))))

(define-fun max () (_ BitVec 17) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) (bvnot (_ bv0 17)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 17)) (b (_ BitVec 17))) (_ BitVec 17)
  (ite (= b (_ bv0 17)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 17))
(declare-fun t () (_ BitVec 17))
(define-fun inv ((s (_ BitVec 17)) (t (_ BitVec 17))) (_ BitVec 17) (bvneg (bvand (bvneg (bvnot t)) (bvneg t))))
(define-fun l ((x (_ BitVec 17))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 17))) (not (= s (_ bv0 17)))) (or (not (= t (bvnot (_ bv0 17)))) (not (= s (bvnot (_ bv0 17)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
