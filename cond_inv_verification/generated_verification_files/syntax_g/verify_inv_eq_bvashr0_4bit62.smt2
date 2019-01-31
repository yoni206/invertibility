
(set-logic QF_BV)

(define-fun min () (_ BitVec 62) (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62))))

(define-fun max () (_ BitVec 62) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) (bvnot (_ bv0 62)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 62))
(declare-fun t () (_ BitVec 62))
(define-fun inv ((s (_ BitVec 62)) (t (_ BitVec 62))) (_ BitVec 62) (bvshl t (bvlshr (bvshl s s) s)))
(define-fun l ((x (_ BitVec 62))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv62 62)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv62 62)) (or (= t (bvnot (_ bv0 62))) (= t (_ bv0 62))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
