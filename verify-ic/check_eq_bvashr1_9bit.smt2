(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 9))
(declare-fun t () (_ BitVec 9))

(define-fun udivtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) (bvnot (_ bv0 9)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 9)) (b (_ BitVec 9))) (_ BitVec 9)
  (ite (= b (_ bv0 9)) a (bvurem a b))
)
(define-fun min () (_ BitVec 9)
  (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9)))
)
(define-fun max () (_ BitVec 9)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 9)) (t (_ BitVec 9))) Bool
(or  (= (bvashr s (_ bv0 9)) t) (= (bvashr s (_ bv1 9)) t) (= (bvashr s (_ bv2 9)) t) (= (bvashr s (_ bv3 9)) t) (= (bvashr s (_ bv4 9)) t) (= (bvashr s (_ bv5 9)) t) (= (bvashr s (_ bv6 9)) t) (= (bvashr s (_ bv7 9)) t) (= (bvashr s (_ bv8 9)) t) (= (bvashr s (_ bv9 9)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 9))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 9))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
