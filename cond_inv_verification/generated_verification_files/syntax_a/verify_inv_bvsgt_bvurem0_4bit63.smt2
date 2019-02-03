
(set-logic QF_BV)

(define-fun min () (_ BitVec 63) (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63))))

(define-fun max () (_ BitVec 63) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))
(define-fun inv ((s (_ BitVec 63)) (t (_ BitVec 63))) (_ BitVec 63) (bvneg (bvnot t)))
(define-fun l ((x (_ BitVec 63))) Bool  (bvsgt (uremtotal (inv s t) s) t))
(define-fun SC () Bool (and (and (=> (bvsgt s (_ bv0 63)) (bvslt t (bvnot (bvneg s)))) (=> (bvsle s (_ bv0 63)) (distinct t max))) (or (distinct t (_ bv0 63)) (distinct s (_ bv1 63)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)