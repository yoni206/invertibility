
(set-logic QF_BV)

(define-fun min () (_ BitVec 25) (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25))))

(define-fun max () (_ BitVec 25) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) (bvnot (_ bv0 25)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 25)) (b (_ BitVec 25))) (_ BitVec 25)
  (ite (= b (_ bv0 25)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 25))
(declare-fun t () (_ BitVec 25))
(define-fun inv ((s (_ BitVec 25)) (t (_ BitVec 25))) (_ BitVec 25) (bvneg (bvand (bvneg t) (bvneg (bvnot t)))))
(define-fun l ((x (_ BitVec 25))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 25))) (not (= s (_ bv0 25)))) (or (not (= t (bvnot (_ bv0 25)))) (not (= s (bvnot (_ bv0 25)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
