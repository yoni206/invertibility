
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
(define-fun inv ((s (_ BitVec 55)) (t (_ BitVec 55))) (_ BitVec 55) (bvnot s))
(define-fun l ((x (_ BitVec 55))) Bool  (bvuge (bvadd (inv s t) s) t))
(define-fun SC () Bool true)
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
