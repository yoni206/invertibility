
(set-logic QF_BV)

(define-fun min () (_ BitVec 43) (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43))))

(define-fun max () (_ BitVec 43) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) (bvnot (_ bv0 43)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 43))
(declare-fun t () (_ BitVec 43))
(define-fun inv ((s (_ BitVec 43)) (t (_ BitVec 43))) (_ BitVec 43) (bvnot (bvor s #b0111111111111111111111111111111111111111111)))
(define-fun l ((x (_ BitVec 43))) Bool  (bvslt (bvashr s (inv s t)) t))
(define-fun SC () Bool (or (bvslt s t) (bvslt (_ bv0 43) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)