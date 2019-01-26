
(set-logic QF_BV)

(define-fun min () (_ BitVec 30) (bvnot (bvlshr (bvnot (_ bv0 30)) (_ bv1 30))))

(define-fun max () (_ BitVec 30) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) (bvnot (_ bv0 30)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 30))
(declare-fun t () (_ BitVec 30))
(define-fun inv ((s (_ BitVec 30)) (t (_ BitVec 30))) (_ BitVec 30) (bvadd #b100000000000000000000000000000 #b011111111111111111111111111111))
(define-fun l ((x (_ BitVec 30))) Bool  (bvule (udivtotal s (inv s t)) t))
(define-fun SC () Bool (bvult (_ bv0 30) (bvor (bvnot s) t)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
