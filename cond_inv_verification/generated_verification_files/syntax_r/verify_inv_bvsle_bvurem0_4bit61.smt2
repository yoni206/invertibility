
(set-logic QF_BV)

(define-fun min () (_ BitVec 61) (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61))))

(define-fun max () (_ BitVec 61) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) (bvnot (_ bv0 61)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 61))
(declare-fun t () (_ BitVec 61))
(define-fun inv ((s (_ BitVec 61)) (t (_ BitVec 61))) (_ BitVec 61) (bvand t #b1000000000000000000000000000000000000000000000000000000000000))
(define-fun l ((x (_ BitVec 61))) Bool  (bvsle (uremtotal (inv s t) s) t))
(define-fun SC () Bool (bvslt (bvnot (_ bv0 61)) (bvand (bvneg s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
