
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
(define-fun inv ((s (_ BitVec 12)) (t (_ BitVec 12))) (_ BitVec 12) (bvnot #b000000000000))
(define-fun l ((x (_ BitVec 12))) Bool  (bvuge (bvashr (inv s t) s) t))
(define-fun SC () Bool true)
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
