
(set-logic QF_BV)

(define-fun min () (_ BitVec 5) (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5))))

(define-fun max () (_ BitVec 5) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(define-fun inv ((s (_ BitVec 5)) (t (_ BitVec 5))) (_ BitVec 5) (bvneg (bvnot (bvlshr s (bvlshr #b01111 (bvsub #b10000 #b01111))))))
(define-fun l ((x (_ BitVec 5))) Bool  (bvsgt (udivtotal s (inv s t)) t))
(define-fun SC () Bool (and (=> (bvsge s (_ bv0 5)) (bvsgt s t)) (=> (bvslt s (_ bv0 5)) (bvsgt (bvlshr s (_ bv1 5)) t))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
