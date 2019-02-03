
(set-logic QF_BV)

(define-fun min () (_ BitVec 20) (bvnot (bvlshr (bvnot (_ bv0 20)) (_ bv1 20))))

(define-fun max () (_ BitVec 20) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) (bvnot (_ bv0 20)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 20)) (b (_ BitVec 20))) (_ BitVec 20)
  (ite (= b (_ bv0 20)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 20))
(declare-fun t () (_ BitVec 20))
(define-fun inv ((s (_ BitVec 20)) (t (_ BitVec 20))) (_ BitVec 20) (bvlshr s (bvlshr #b01111111111111111111 (bvsub #b10000000000000000000 #b01111111111111111111))))
(define-fun l ((x (_ BitVec 20))) Bool  (bvsgt (bvlshr s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvslt s (_ bv0 20)) (bvsgt (bvlshr s (_ bv1 20)) t)) (=> (bvsge s (_ bv0 20)) (bvsgt s t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)