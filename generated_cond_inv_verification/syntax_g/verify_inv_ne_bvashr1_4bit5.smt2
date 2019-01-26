
(set-logic QF_BV)

(define-fun min () (_ BitVec 5) (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5))))

(define-fun max () (_ BitVec 5) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(define-fun inv ((s (_ BitVec 5)) (t (_ BitVec 5))) (_ BitVec 5) (bvlshr t (bvsub s t)))
(define-fun l ((x (_ BitVec 5))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 5))) (not (= s (_ bv0 5)))) (or (not (= t (bvnot (_ bv0 5)))) (not (= s (bvnot (_ bv0 5)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
