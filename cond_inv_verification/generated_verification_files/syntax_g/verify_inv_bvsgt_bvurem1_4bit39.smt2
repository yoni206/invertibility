
(set-logic QF_BV)

(define-fun min () (_ BitVec 39) (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39))))

(define-fun max () (_ BitVec 39) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) (bvnot (_ bv0 39)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 39)) (b (_ BitVec 39))) (_ BitVec 39)
  (ite (= b (_ bv0 39)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 39))
(declare-fun t () (_ BitVec 39))
(define-fun inv ((s (_ BitVec 39)) (t (_ BitVec 39))) (_ BitVec 39) (bvsub (bvor s #b100000000000000000000000000000000000000) (bvand #b011111111111111111111111111111111111111 (bvsub t #b011111111111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 39))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 39)) (bvsgt s t)) (=> (bvslt s (_ bv0 39)) (bvsgt (bvlshr (bvsub s (_ bv1 39)) (_ bv1 39)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
