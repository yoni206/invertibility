
(set-logic QF_BV)

(define-fun min () (_ BitVec 28) (bvnot (bvlshr (bvnot (_ bv0 28)) (_ bv1 28))))

(define-fun max () (_ BitVec 28) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) (bvnot (_ bv0 28)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 28)) (b (_ BitVec 28))) (_ BitVec 28)
  (ite (= b (_ bv0 28)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 28))
(declare-fun t () (_ BitVec 28))
(define-fun inv ((s (_ BitVec 28)) (t (_ BitVec 28))) (_ BitVec 28) (bvneg (bvand (bvneg (bvnot t)) (bvneg t))))
(define-fun l ((x (_ BitVec 28))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 28))) (not (= s (_ bv0 28)))) (or (not (= t (bvnot (_ bv0 28)))) (not (= s (bvnot (_ bv0 28)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
