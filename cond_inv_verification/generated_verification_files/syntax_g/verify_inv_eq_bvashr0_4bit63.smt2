
(set-logic QF_BV)

(define-fun min () (_ BitVec 63) (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63))))

(define-fun max () (_ BitVec 63) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))
(define-fun inv ((s (_ BitVec 63)) (t (_ BitVec 63))) (_ BitVec 63) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 63))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv63 63)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv63 63)) (or (= t (bvnot (_ bv0 63))) (= t (_ bv0 63))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
