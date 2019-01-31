
(set-logic QF_BV)

(define-fun min () (_ BitVec 49) (bvnot (bvlshr (bvnot (_ bv0 49)) (_ bv1 49))))

(define-fun max () (_ BitVec 49) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) (bvnot (_ bv0 49)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 49))
(declare-fun t () (_ BitVec 49))
(define-fun inv ((s (_ BitVec 49)) (t (_ BitVec 49))) (_ BitVec 49) (bvnot (bvneg t)))
(define-fun l ((x (_ BitVec 49))) Bool  (distinct (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (distinct s (_ bv0 49)) (distinct t (bvnot (_ bv0 49)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
