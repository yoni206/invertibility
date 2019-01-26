
(set-logic QF_BV)

(define-fun min () (_ BitVec 15) (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15))))

(define-fun max () (_ BitVec 15) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) (bvnot (_ bv0 15)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 15)) (b (_ BitVec 15))) (_ BitVec 15)
  (ite (= b (_ bv0 15)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 15))
(declare-fun t () (_ BitVec 15))
(define-fun inv ((s (_ BitVec 15)) (t (_ BitVec 15))) (_ BitVec 15) (bvadd (bvmul s t) #b011111111111111))
(define-fun l ((x (_ BitVec 15))) Bool  (bvsge (bvlshr (inv s t) s) t))
(define-fun SC () Bool (=> (not (= s (_ bv0 15))) (bvsge (bvlshr (bvnot (_ bv0 15)) s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
