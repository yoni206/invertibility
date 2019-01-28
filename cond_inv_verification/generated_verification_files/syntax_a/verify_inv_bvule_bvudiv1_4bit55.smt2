
(set-logic QF_BV)

(define-fun min () (_ BitVec 55) (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55))))

(define-fun max () (_ BitVec 55) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) (bvnot (_ bv0 55)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 55))
(declare-fun t () (_ BitVec 55))
(define-fun inv ((s (_ BitVec 55)) (t (_ BitVec 55))) (_ BitVec 55) (bvnot #b0000000000000000000000000000000000000000000000000000000))
(define-fun l ((x (_ BitVec 55))) Bool  (bvule (udivtotal s (inv s t)) t))
(define-fun SC () Bool (bvult (_ bv0 55) (bvor (bvnot s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
