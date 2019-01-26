
(set-logic QF_BV)

(define-fun min () (_ BitVec 23) (bvnot (bvlshr (bvnot (_ bv0 23)) (_ bv1 23))))

(define-fun max () (_ BitVec 23) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) (bvnot (_ bv0 23)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 23)) (b (_ BitVec 23))) (_ BitVec 23)
  (ite (= b (_ bv0 23)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 23))
(declare-fun t () (_ BitVec 23))
(define-fun inv ((s (_ BitVec 23)) (t (_ BitVec 23))) (_ BitVec 23) (bvand (bvnot s) #b10000000000000000000000))
(define-fun l ((x (_ BitVec 23))) Bool  (bvslt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 23) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
