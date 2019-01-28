
(set-logic QF_BV)

(define-fun min () (_ BitVec 35) (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35))))

(define-fun max () (_ BitVec 35) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))
(define-fun inv ((s (_ BitVec 35)) (t (_ BitVec 35))) (_ BitVec 35) (bvsub (bvor s #b10000000000000000000000000000000000) (bvand #b01111111111111111111111111111111111 (bvsub t #b01111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 35))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 35)) (bvsgt s t)) (=> (bvslt s (_ bv0 35)) (bvsgt (bvlshr (bvsub s (_ bv1 35)) (_ bv1 35)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
