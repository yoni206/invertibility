
(set-logic QF_BV)

(define-fun min () (_ BitVec 34) (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34))))

(define-fun max () (_ BitVec 34) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) (bvnot (_ bv0 34)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 34)) (b (_ BitVec 34))) (_ BitVec 34)
  (ite (= b (_ bv0 34)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 34))
(declare-fun t () (_ BitVec 34))
(define-fun inv ((s (_ BitVec 34)) (t (_ BitVec 34))) (_ BitVec 34) (bvsub #b0111111111111111111111111111111111 s))
(define-fun l ((x (_ BitVec 34))) Bool  (bvsgt (bvadd (inv s t) s) t))
(define-fun SC () Bool (distinct t max))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
