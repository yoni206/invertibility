
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
(define-fun inv ((s (_ BitVec 30)) (t (_ BitVec 30))) (_ BitVec 30) #b000000000000000000000000000000)
(define-fun l ((x (_ BitVec 30))) Bool  (bvuge (uremtotal s (inv s t)) t))
(define-fun SC () Bool (or (bvuge (bvand (bvsub (bvadd t t) s) s) t) (bvult t s)))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
