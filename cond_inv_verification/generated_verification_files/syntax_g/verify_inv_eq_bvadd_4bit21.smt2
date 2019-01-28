
(set-logic QF_BV)

(define-fun min () (_ BitVec 21) (bvnot (bvlshr (bvnot (_ bv0 21)) (_ bv1 21))))

(define-fun max () (_ BitVec 21) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) (bvnot (_ bv0 21)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 21)) (b (_ BitVec 21))) (_ BitVec 21)
  (ite (= b (_ bv0 21)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 21))
(declare-fun t () (_ BitVec 21))
(define-fun inv ((s (_ BitVec 21)) (t (_ BitVec 21))) (_ BitVec 21) (bvsub t s))
(define-fun l ((x (_ BitVec 21))) Bool  (= (bvadd (inv s t) s) t))
(define-fun SC () Bool true)
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
