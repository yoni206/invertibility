
(set-logic QF_BV)

(define-fun min () (_ BitVec 37) (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37))))

(define-fun max () (_ BitVec 37) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) (bvnot (_ bv0 37)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 37)) (b (_ BitVec 37))) (_ BitVec 37)
  (ite (= b (_ bv0 37)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 37))
(declare-fun t () (_ BitVec 37))
(define-fun inv ((s (_ BitVec 37)) (t (_ BitVec 37))) (_ BitVec 37) (bvnot (bvneg t)))
(define-fun l ((x (_ BitVec 37))) Bool  (distinct (bvlshr (inv s t) s) t))
(define-fun SC () Bool (or (distinct t (_ bv0 37)) (bvult s (_ bv37 37))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
