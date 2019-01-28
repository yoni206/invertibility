
(set-logic QF_BV)

(define-fun min () (_ BitVec 5) (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5))))

(define-fun max () (_ BitVec 5) (bvnot min))

(define-fun udivtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) (bvnot (_ bv0 5)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 5)) (b (_ BitVec 5))) (_ BitVec 5)
  (ite (= b (_ bv0 5)) a (bvurem a b))
)

(declare-fun s () (_ BitVec 5))
(declare-fun t () (_ BitVec 5))
(define-fun inv ((s (_ BitVec 5)) (t (_ BitVec 5))) (_ BitVec 5) (bvmul t (bvsub s (bvnot (bvmul s (bvmul t (bvmul t t)))))))
(define-fun l ((x (_ BitVec 5))) Bool  (= (bvashr (inv s t) s) t))
(define-fun SC () Bool (and (=> (bvult s (_ bv5 5)) (= (bvashr (bvshl t s) s) t)) (=> (bvuge s (_ bv5 5)) (or (= t (bvnot (_ bv0 5))) (= t (_ bv0 5))))))
(define-fun is_cond_inv () Bool (=> SC (l (inv s t))))

(assert (not is_cond_inv))
(check-sat)
