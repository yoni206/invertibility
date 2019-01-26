
(set-logic QF_BV)

(define-fun min () (_ BitVec 31) (bvnot (bvlshr (bvnot (_ bv0 31)) (_ bv1 31))))

(define-fun max () (_ BitVec 31) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 31)) (b (_ BitVec 31))) (_ BitVec 31)
  (ite (= b (_ bv0 31)) (bvnot (_ bv0 31)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 31)) (b (_ BitVec 31))) (_ BitVec 31)
  (ite (= b (_ bv0 31)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 31))
(declare-fun t () (_ BitVec 31))
(define-fun inv ((s (_ BitVec 31)) (t (_ BitVec 31))) (_ BitVec 31) (bvlshr s (bvlshr #b0111111111111111111111111111111 (bvsub #b1000000000000000000000000000000 #b0111111111111111111111111111111))))
(define-fun l ((x (_ BitVec 31))) Bool  (bvsge (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 31)) (bvsge (bvlshr s (_ bv1 31)) t)) (=> (bvsge s (_ bv0 31)) (bvsge s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
