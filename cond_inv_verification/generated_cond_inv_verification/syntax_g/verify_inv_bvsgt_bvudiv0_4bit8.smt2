
(set-logic QF_BV)

(define-fun min () (_ BitVec 8) (bvnot (bvlshr (bvnot (_ bv0 8)) (_ bv1 8))))

(define-fun max () (_ BitVec 8) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 8)
  (ite (= b (_ bv0 8)) (bvnot (_ bv0 8)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 8)) (b (_ BitVec 8))) (_ BitVec 8)
  (ite (= b (_ bv0 8)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 8))
(declare-fun t () (_ BitVec 8))
(define-fun inv ((s (_ BitVec 8)) (t (_ BitVec 8))) (_ BitVec 8) (bvor (bvsub (bvlshr (bvneg s) s) #b01111111) #b01111111))
(define-fun l ((x (_ BitVec 8))) Bool  (bvsgt (udivtotal (inv s t) s) t))
(define-fun SC () Bool (or (bvsgt (udivtotal (bvnot (_ bv0 8)) s) t) (bvsgt (udivtotal max s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
