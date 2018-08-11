(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 30))
(declare-fun t () (_ BitVec 30))

(define-fun udivtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) (bvnot (_ bv0 30)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 30)) (b (_ BitVec 30))) (_ BitVec 30)
  (ite (= b (_ bv0 30)) a (bvurem a b))
)
(define-fun min () (_ BitVec 30)
  (bvnot (bvlshr (bvnot (_ bv0 30)) (_ bv1 30)))
)
(define-fun max () (_ BitVec 30)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 30)) (t (_ BitVec 30))) Bool
(or  (bvsge (bvshl s (_ bv0 30)) t) (bvsge (bvshl s (_ bv1 30)) t) (bvsge (bvshl s (_ bv2 30)) t) (bvsge (bvshl s (_ bv3 30)) t) (bvsge (bvshl s (_ bv4 30)) t) (bvsge (bvshl s (_ bv5 30)) t) (bvsge (bvshl s (_ bv6 30)) t) (bvsge (bvshl s (_ bv7 30)) t) (bvsge (bvshl s (_ bv8 30)) t) (bvsge (bvshl s (_ bv9 30)) t) (bvsge (bvshl s (_ bv10 30)) t) (bvsge (bvshl s (_ bv11 30)) t) (bvsge (bvshl s (_ bv12 30)) t) (bvsge (bvshl s (_ bv13 30)) t) (bvsge (bvshl s (_ bv14 30)) t) (bvsge (bvshl s (_ bv15 30)) t) (bvsge (bvshl s (_ bv16 30)) t) (bvsge (bvshl s (_ bv17 30)) t) (bvsge (bvshl s (_ bv18 30)) t) (bvsge (bvshl s (_ bv19 30)) t) (bvsge (bvshl s (_ bv20 30)) t) (bvsge (bvshl s (_ bv21 30)) t) (bvsge (bvshl s (_ bv22 30)) t) (bvsge (bvshl s (_ bv23 30)) t) (bvsge (bvshl s (_ bv24 30)) t) (bvsge (bvshl s (_ bv25 30)) t) (bvsge (bvshl s (_ bv26 30)) t) (bvsge (bvshl s (_ bv27 30)) t) (bvsge (bvshl s (_ bv28 30)) t) (bvsge (bvshl s (_ bv29 30)) t) (bvsge (bvshl s (_ bv30 30)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 30))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 30))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
