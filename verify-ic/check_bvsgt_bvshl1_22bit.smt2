(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 22))
(declare-fun t () (_ BitVec 22))

(define-fun udivtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) (bvnot (_ bv0 22)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 22)) (b (_ BitVec 22))) (_ BitVec 22)
  (ite (= b (_ bv0 22)) a (bvurem a b))
)
(define-fun min () (_ BitVec 22)
  (bvnot (bvlshr (bvnot (_ bv0 22)) (_ bv1 22)))
)
(define-fun max () (_ BitVec 22)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 22)) (t (_ BitVec 22))) Bool
(or  (bvsgt (bvshl s (_ bv0 22)) t) (bvsgt (bvshl s (_ bv1 22)) t) (bvsgt (bvshl s (_ bv2 22)) t) (bvsgt (bvshl s (_ bv3 22)) t) (bvsgt (bvshl s (_ bv4 22)) t) (bvsgt (bvshl s (_ bv5 22)) t) (bvsgt (bvshl s (_ bv6 22)) t) (bvsgt (bvshl s (_ bv7 22)) t) (bvsgt (bvshl s (_ bv8 22)) t) (bvsgt (bvshl s (_ bv9 22)) t) (bvsgt (bvshl s (_ bv10 22)) t) (bvsgt (bvshl s (_ bv11 22)) t) (bvsgt (bvshl s (_ bv12 22)) t) (bvsgt (bvshl s (_ bv13 22)) t) (bvsgt (bvshl s (_ bv14 22)) t) (bvsgt (bvshl s (_ bv15 22)) t) (bvsgt (bvshl s (_ bv16 22)) t) (bvsgt (bvshl s (_ bv17 22)) t) (bvsgt (bvshl s (_ bv18 22)) t) (bvsgt (bvshl s (_ bv19 22)) t) (bvsgt (bvshl s (_ bv20 22)) t) (bvsgt (bvshl s (_ bv21 22)) t) (bvsgt (bvshl s (_ bv22 22)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 22))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 22))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
