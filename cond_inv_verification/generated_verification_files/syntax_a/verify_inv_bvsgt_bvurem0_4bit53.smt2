
(set-logic QF_BV)

(define-fun min () (_ BitVec 53) (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53))))

(define-fun max () (_ BitVec 53) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) (bvnot (_ bv0 53)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 53))
(declare-fun t () (_ BitVec 53))
(define-fun inv ((s (_ BitVec 53)) (t (_ BitVec 53))) (_ BitVec 53) (bvneg (bvnot t)))
(define-fun l ((x (_ BitVec 53))) Bool  (bvsgt (uremtotal (inv s t) s) t))
(define-fun SC () Bool (and (and (=> (bvsgt s (_ bv0 53)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 53)) (distinct t max))) (or (distinct t (_ bv0 53)) (distinct s (_ bv1 53)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
