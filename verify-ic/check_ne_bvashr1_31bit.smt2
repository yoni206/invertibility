(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 31))
(declare-fun t () (_ BitVec 31))

(define-fun udivtotal ((a (_ BitVec 31)) (b (_ BitVec 31))) (_ BitVec 31)
  (ite (= b (_ bv0 31)) (bvnot (_ bv0 31)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 31)) (b (_ BitVec 31))) (_ BitVec 31)
  (ite (= b (_ bv0 31)) a (bvurem a b))
)
(define-fun min () (_ BitVec 31)
  (bvnot (bvlshr (bvnot (_ bv0 31)) (_ bv1 31)))
)
(define-fun max () (_ BitVec 31)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 31)) (t (_ BitVec 31))) Bool
(and (or (not (= t (_ bv0 31))) (not (= s (_ bv0 31)))) (or (not (= t (bvnot (_ bv0 31)))) (not (= s (bvnot (_ bv0 31))))))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 31))) (distinct (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 31))) (distinct (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
