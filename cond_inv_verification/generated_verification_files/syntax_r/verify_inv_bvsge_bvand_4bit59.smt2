
(set-logic QF_BV)

(define-fun min () (_ BitVec 59) (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59))))

(define-fun max () (_ BitVec 59) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) (bvnot (_ bv0 59)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 59))
(declare-fun t () (_ BitVec 59))
(define-fun inv ((s (_ BitVec 59)) (t (_ BitVec 59))) (_ BitVec 59) #b01111111111111111111111111111111111111111111111111111111111)
(define-fun l ((x (_ BitVec 59))) Bool  (bvsge (bvand (inv s t) s) t))
(define-fun SC () Bool (or (= (bvand s t) t) (bvslt t (bvand (bvsub t s) s))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
