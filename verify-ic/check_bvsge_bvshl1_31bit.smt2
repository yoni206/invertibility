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
(or  (bvsge (bvshl s (_ bv0 31)) t) (bvsge (bvshl s (_ bv1 31)) t) (bvsge (bvshl s (_ bv2 31)) t) (bvsge (bvshl s (_ bv3 31)) t) (bvsge (bvshl s (_ bv4 31)) t) (bvsge (bvshl s (_ bv5 31)) t) (bvsge (bvshl s (_ bv6 31)) t) (bvsge (bvshl s (_ bv7 31)) t) (bvsge (bvshl s (_ bv8 31)) t) (bvsge (bvshl s (_ bv9 31)) t) (bvsge (bvshl s (_ bv10 31)) t) (bvsge (bvshl s (_ bv11 31)) t) (bvsge (bvshl s (_ bv12 31)) t) (bvsge (bvshl s (_ bv13 31)) t) (bvsge (bvshl s (_ bv14 31)) t) (bvsge (bvshl s (_ bv15 31)) t) (bvsge (bvshl s (_ bv16 31)) t) (bvsge (bvshl s (_ bv17 31)) t) (bvsge (bvshl s (_ bv18 31)) t) (bvsge (bvshl s (_ bv19 31)) t) (bvsge (bvshl s (_ bv20 31)) t) (bvsge (bvshl s (_ bv21 31)) t) (bvsge (bvshl s (_ bv22 31)) t) (bvsge (bvshl s (_ bv23 31)) t) (bvsge (bvshl s (_ bv24 31)) t) (bvsge (bvshl s (_ bv25 31)) t) (bvsge (bvshl s (_ bv26 31)) t) (bvsge (bvshl s (_ bv27 31)) t) (bvsge (bvshl s (_ bv28 31)) t) (bvsge (bvshl s (_ bv29 31)) t) (bvsge (bvshl s (_ bv30 31)) t) (bvsge (bvshl s (_ bv31 31)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 31))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 31))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
