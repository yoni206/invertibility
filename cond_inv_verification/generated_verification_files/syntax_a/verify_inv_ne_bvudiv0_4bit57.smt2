
(set-logic QF_BV)

(define-fun min () (_ BitVec 57) (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57))))

(define-fun max () (_ BitVec 57) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) (bvnot (_ bv0 57)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 57))
(declare-fun t () (_ BitVec 57))
(define-fun inv ((s (_ BitVec 57)) (t (_ BitVec 57))) (_ BitVec 57) (bvnot (bvneg t)))
(define-fun l ((x (_ BitVec 57))) Bool  (distinct (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (distinct s (_ bv0 57)) (distinct t (bvnot (_ bv0 57)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
