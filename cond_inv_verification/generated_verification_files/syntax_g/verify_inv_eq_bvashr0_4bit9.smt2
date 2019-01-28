
(set-logic QF_BV)

(define-fun min () (_ BitVec 9) (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9))))

(define-fun max () (_ BitVec 9) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) (bvnot (_ bv0 9)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 9))
(declare-fun t () (_ BitVec 9))
(define-fun inv ((s (_ BitVec 9)) (t (_ BitVec 9))) (_ BitVec 9) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 9))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv9 9)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv9 9)) (or (= t (bvnot (_ bv0 9))) (= t (_ bv0 9))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
