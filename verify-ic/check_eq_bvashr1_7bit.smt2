(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun t () (_ BitVec 7))

(define-fun udivtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) (bvnot (_ bv0 7)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 7)) (b (_ BitVec 7))) (_ BitVec 7)
  (ite (= b (_ bv0 7)) a (bvurem a b))
)
(define-fun min () (_ BitVec 7)
  (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7)))
)
(define-fun max () (_ BitVec 7)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 7)) (t (_ BitVec 7))) Bool
(or  (= (bvashr s (_ bv0 7)) t) (= (bvashr s (_ bv1 7)) t) (= (bvashr s (_ bv2 7)) t) (= (bvashr s (_ bv3 7)) t) (= (bvashr s (_ bv4 7)) t) (= (bvashr s (_ bv5 7)) t) (= (bvashr s (_ bv6 7)) t) (= (bvashr s (_ bv7 7)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 7))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 7))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
