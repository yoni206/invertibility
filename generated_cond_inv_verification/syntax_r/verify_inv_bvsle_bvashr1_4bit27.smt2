
(set-logic QF_BV)

(define-fun min () (_ BitVec 27) (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27))))

(define-fun max () (_ BitVec 27) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) (bvnot (_ bv0 27)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 27)) (b (_ BitVec 27))) (_ BitVec 27)
  (ite (= b (_ bv0 27)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 27))
(declare-fun t () (_ BitVec 27))
(define-fun inv ((s (_ BitVec 27)) (t (_ BitVec 27))) (_ BitVec 27) (bvand (bvnot s) #b100000000000000000000000000))
(define-fun l ((x (_ BitVec 27))) Bool  (bvsle (bvashr s (inv s t)) t))
(define-fun SC () Bool (or (bvsge t (_ bv0 27)) (bvsge t s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
