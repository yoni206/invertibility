
(set-logic QF_BV)

(define-fun min () (_ BitVec 45) (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45))))

(define-fun max () (_ BitVec 45) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))
(define-fun inv ((s (_ BitVec 45)) (t (_ BitVec 45))) (_ BitVec 45) (bvnot #b000000000000000000000000000000000000000000000))
(define-fun l ((x (_ BitVec 45))) Bool  (bvuge (udivtotal (inv s t) s) t))
(define-fun SC () Bool (= (bvand (udivtotal (bvmul s t) t) s) s))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
