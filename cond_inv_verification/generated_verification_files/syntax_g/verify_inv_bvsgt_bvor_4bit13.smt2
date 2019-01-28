
(set-logic QF_BV)

(define-fun min () (_ BitVec 13) (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13))))

(define-fun max () (_ BitVec 13) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) (bvnot (_ bv0 13)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 13)) (b (_ BitVec 13))) (_ BitVec 13)
  (ite (= b (_ bv0 13)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 13))
(declare-fun t () (_ BitVec 13))
(define-fun inv ((s (_ BitVec 13)) (t (_ BitVec 13))) (_ BitVec 13) #b0111111111111)
(define-fun l ((x (_ BitVec 13))) Bool  (bvsgt (bvor (inv s t) s) t))
(define-fun SC () Bool (bvslt t (bvor s max)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
