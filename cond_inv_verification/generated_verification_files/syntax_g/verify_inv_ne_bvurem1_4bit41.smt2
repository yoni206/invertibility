
(set-logic QF_BV)

(define-fun min () (_ BitVec 41) (bvnot (bvlshr (bvnot (_ bv0 41)) (_ bv1 41))))

(define-fun max () (_ BitVec 41) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) (bvnot (_ bv0 41)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 41)) (b (_ BitVec 41))) (_ BitVec 41)
  (ite (= b (_ bv0 41)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 41))
(declare-fun t () (_ BitVec 41))
(define-fun inv ((s (_ BitVec 41)) (t (_ BitVec 41))) (_ BitVec 41) t)
(define-fun l ((x (_ BitVec 41))) Bool  (distinct (uremtotal s (inv s t)) t))
(define-fun SC () Bool (or (distinct s (_ bv0 41)) (distinct t (_ bv0 41))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
