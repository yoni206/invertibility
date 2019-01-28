
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
(define-fun inv ((s (_ BitVec 33)) (t (_ BitVec 33))) (_ BitVec 33) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 33))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv33 33)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv33 33)) (or (= t (bvnot (_ bv0 33))) (= t (_ bv0 33))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
