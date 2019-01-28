
(set-logic QF_BV)

(define-fun min () (_ BitVec 60) (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60))))

(define-fun max () (_ BitVec 60) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))
(define-fun inv ((s (_ BitVec 60)) (t (_ BitVec 60))) (_ BitVec 60) #b100000000000000000000000000000000000000000000000000000000000)
(define-fun l ((x (_ BitVec 60))) Bool  (bvslt (bvneg (inv s t)) t))
(define-fun SC () Bool (distinct t min))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
