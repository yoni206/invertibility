
(set-logic QF_BV)

(define-fun min () (_ BitVec 64) (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64))))

(define-fun max () (_ BitVec 64) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))
(define-fun inv ((s (_ BitVec 64)) (t (_ BitVec 64))) (_ BitVec 64) (bvneg t))
(define-fun l ((x (_ BitVec 64))) Bool  (distinct (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (distinct s (_ bv0 64)) (distinct t (_ bv0 64))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
