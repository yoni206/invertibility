(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 42))
(declare-fun t () (_ BitVec 42))

(define-fun udivtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) (bvnot (_ bv0 42)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 42)) (b (_ BitVec 42))) (_ BitVec 42)
  (ite (= b (_ bv0 42)) a (bvurem a b))
)
(define-fun min () (_ BitVec 42)
  (bvnot (bvlshr (bvnot (_ bv0 42)) (_ bv1 42)))
)
(define-fun max () (_ BitVec 42)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 42)) (t (_ BitVec 42))) Bool
(or  (bvsge (bvshl s (_ bv0 42)) t) (bvsge (bvshl s (_ bv1 42)) t) (bvsge (bvshl s (_ bv2 42)) t) (bvsge (bvshl s (_ bv3 42)) t) (bvsge (bvshl s (_ bv4 42)) t) (bvsge (bvshl s (_ bv5 42)) t) (bvsge (bvshl s (_ bv6 42)) t) (bvsge (bvshl s (_ bv7 42)) t) (bvsge (bvshl s (_ bv8 42)) t) (bvsge (bvshl s (_ bv9 42)) t) (bvsge (bvshl s (_ bv10 42)) t) (bvsge (bvshl s (_ bv11 42)) t) (bvsge (bvshl s (_ bv12 42)) t) (bvsge (bvshl s (_ bv13 42)) t) (bvsge (bvshl s (_ bv14 42)) t) (bvsge (bvshl s (_ bv15 42)) t) (bvsge (bvshl s (_ bv16 42)) t) (bvsge (bvshl s (_ bv17 42)) t) (bvsge (bvshl s (_ bv18 42)) t) (bvsge (bvshl s (_ bv19 42)) t) (bvsge (bvshl s (_ bv20 42)) t) (bvsge (bvshl s (_ bv21 42)) t) (bvsge (bvshl s (_ bv22 42)) t) (bvsge (bvshl s (_ bv23 42)) t) (bvsge (bvshl s (_ bv24 42)) t) (bvsge (bvshl s (_ bv25 42)) t) (bvsge (bvshl s (_ bv26 42)) t) (bvsge (bvshl s (_ bv27 42)) t) (bvsge (bvshl s (_ bv28 42)) t) (bvsge (bvshl s (_ bv29 42)) t) (bvsge (bvshl s (_ bv30 42)) t) (bvsge (bvshl s (_ bv31 42)) t) (bvsge (bvshl s (_ bv32 42)) t) (bvsge (bvshl s (_ bv33 42)) t) (bvsge (bvshl s (_ bv34 42)) t) (bvsge (bvshl s (_ bv35 42)) t) (bvsge (bvshl s (_ bv36 42)) t) (bvsge (bvshl s (_ bv37 42)) t) (bvsge (bvshl s (_ bv38 42)) t) (bvsge (bvshl s (_ bv39 42)) t) (bvsge (bvshl s (_ bv40 42)) t) (bvsge (bvshl s (_ bv41 42)) t) (bvsge (bvshl s (_ bv42 42)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 42))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 42))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
