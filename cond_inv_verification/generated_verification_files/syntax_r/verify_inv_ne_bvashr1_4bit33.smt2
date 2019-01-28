
(set-logic QF_BV)

(define-fun min () (_ BitVec 33) (bvnot (bvlshr (bvnot (_ bv0 33)) (_ bv1 33))))

(define-fun max () (_ BitVec 33) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) (bvnot (_ bv0 33)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 33)) (b (_ BitVec 33))) (_ BitVec 33)
  (ite (= b (_ bv0 33)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 33))
(declare-fun t () (_ BitVec 33))
(define-fun inv ((s (_ BitVec 33)) (t (_ BitVec 33))) (_ BitVec 33) (bvneg (bvand (bvneg t) (bvneg (bvnot t)))))
(define-fun l ((x (_ BitVec 33))) Bool  (distinct (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (or (not (= t (_ bv0 33))) (not (= s (_ bv0 33)))) (or (not (= t (bvnot (_ bv0 33)))) (not (= s (bvnot (_ bv0 33)))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
