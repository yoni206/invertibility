
(set-logic QF_BV)

(define-fun min () (_ BitVec 11) (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11))))

(define-fun max () (_ BitVec 11) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) (bvnot (_ bv0 11)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 11)) (b (_ BitVec 11))) (_ BitVec 11)
  (ite (= b (_ bv0 11)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 11))
(declare-fun t () (_ BitVec 11))
(define-fun inv ((s (_ BitVec 11)) (t (_ BitVec 11))) (_ BitVec 11) (bvadd (bvand #b10000000000 s) #b10000000000))
(define-fun l ((x (_ BitVec 11))) Bool  (bvult (bvashr s (inv s t)) t))
(define-fun SC () Bool (and (not (and (not (bvult s t)) (bvslt s (_ bv0 11)))) (not (= t (_ bv0 11)))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
