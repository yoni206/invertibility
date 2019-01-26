
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
(define-fun inv ((s (_ BitVec 31)) (t (_ BitVec 31))) (_ BitVec 31) (bvand (bvnot s) #b1000000000000000000000000000000))
(define-fun l ((x (_ BitVec 31))) Bool  (bvule (bvashr s (inv s t)) t))
(define-fun SC () Bool (or (bvult s min) (bvuge t s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
