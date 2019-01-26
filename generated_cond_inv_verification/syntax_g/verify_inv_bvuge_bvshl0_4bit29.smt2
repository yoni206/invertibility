
(set-logic QF_BV)

(define-fun min () (_ BitVec 29) (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29))))

(define-fun max () (_ BitVec 29) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) (bvnot (_ bv0 29)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 29)) (b (_ BitVec 29))) (_ BitVec 29)
  (ite (= b (_ bv0 29)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 29))
(declare-fun t () (_ BitVec 29))
(define-fun inv ((s (_ BitVec 29)) (t (_ BitVec 29))) (_ BitVec 29) (bvnot #b00000000000000000000000000000))
(define-fun l ((x (_ BitVec 29))) Bool  (bvuge (bvshl (inv s t) s) t))
(define-fun SC () Bool (bvuge (bvshl (bvnot (_ bv0 29)) s) t))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
