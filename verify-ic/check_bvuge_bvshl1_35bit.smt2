(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 35))
(declare-fun t () (_ BitVec 35))

(define-fun udivtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) (bvnot (_ bv0 35)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 35)) (b (_ BitVec 35))) (_ BitVec 35)
  (ite (= b (_ bv0 35)) a (bvurem a b))
)
(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 35)) (t (_ BitVec 35))) Bool
(or  (bvuge (bvshl s (_ bv0 35)) t) (bvuge (bvshl s (_ bv1 35)) t) (bvuge (bvshl s (_ bv2 35)) t) (bvuge (bvshl s (_ bv3 35)) t) (bvuge (bvshl s (_ bv4 35)) t) (bvuge (bvshl s (_ bv5 35)) t) (bvuge (bvshl s (_ bv6 35)) t) (bvuge (bvshl s (_ bv7 35)) t) (bvuge (bvshl s (_ bv8 35)) t) (bvuge (bvshl s (_ bv9 35)) t) (bvuge (bvshl s (_ bv10 35)) t) (bvuge (bvshl s (_ bv11 35)) t) (bvuge (bvshl s (_ bv12 35)) t) (bvuge (bvshl s (_ bv13 35)) t) (bvuge (bvshl s (_ bv14 35)) t) (bvuge (bvshl s (_ bv15 35)) t) (bvuge (bvshl s (_ bv16 35)) t) (bvuge (bvshl s (_ bv17 35)) t) (bvuge (bvshl s (_ bv18 35)) t) (bvuge (bvshl s (_ bv19 35)) t) (bvuge (bvshl s (_ bv20 35)) t) (bvuge (bvshl s (_ bv21 35)) t) (bvuge (bvshl s (_ bv22 35)) t) (bvuge (bvshl s (_ bv23 35)) t) (bvuge (bvshl s (_ bv24 35)) t) (bvuge (bvshl s (_ bv25 35)) t) (bvuge (bvshl s (_ bv26 35)) t) (bvuge (bvshl s (_ bv27 35)) t) (bvuge (bvshl s (_ bv28 35)) t) (bvuge (bvshl s (_ bv29 35)) t) (bvuge (bvshl s (_ bv30 35)) t) (bvuge (bvshl s (_ bv31 35)) t) (bvuge (bvshl s (_ bv32 35)) t) (bvuge (bvshl s (_ bv33 35)) t) (bvuge (bvshl s (_ bv34 35)) t) (bvuge (bvshl s (_ bv35 35)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 35))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 35))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
