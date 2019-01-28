
(set-logic QF_BV)

(define-fun min () (_ BitVec 12) (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12))))

(define-fun max () (_ BitVec 12) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) (bvnot (_ bv0 12)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 12)) (b (_ BitVec 12))) (_ BitVec 12)
  (ite (= b (_ bv0 12)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 12))
(declare-fun t () (_ BitVec 12))
(define-fun inv ((s (_ BitVec 12)) (t (_ BitVec 12))) (_ BitVec 12) (bvsub (bvor s #b100000000000) (bvand #b011111111111 (bvsub t #b011111111111))))
(define-fun l ((x (_ BitVec 12))) Bool  (bvsgt (uremtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 12)) (bvsgt s t)) (=> (bvslt s (_ bv0 12)) (bvsgt (bvlshr (bvsub s (_ bv1 12)) (_ bv1 12)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
