
(set-logic QF_BV)

(define-fun min () (_ BitVec 39) (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39))))

(define-fun max () (_ BitVec 39) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) (bvnot (_ bv0 39)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 39))
(declare-fun t () (_ BitVec 39))
(define-fun inv ((s (_ BitVec 39)) (t (_ BitVec 39))) (_ BitVec 39) (bvlshr t (bvsub s t)))
(define-fun l ((x (_ BitVec 39))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 39))) (not (= s (_ bv0 39)))) (or (not (= t (bvnot (_ bv0 39)))) (not (= s (bvnot (_ bv0 39)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
