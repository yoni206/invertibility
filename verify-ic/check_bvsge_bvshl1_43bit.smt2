(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 43))
(declare-fun t () (_ BitVec 43))

(define-fun udivtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) (bvnot (_ bv0 43)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 43)) (b (_ BitVec 43))) (_ BitVec 43)
  (ite (= b (_ bv0 43)) a (bvurem a b))
)
(define-fun min () (_ BitVec 43)
  (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43)))
)
(define-fun max () (_ BitVec 43)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 43)) (t (_ BitVec 43))) Bool
(or  (bvsge (bvshl s (_ bv0 43)) t) (bvsge (bvshl s (_ bv1 43)) t) (bvsge (bvshl s (_ bv2 43)) t) (bvsge (bvshl s (_ bv3 43)) t) (bvsge (bvshl s (_ bv4 43)) t) (bvsge (bvshl s (_ bv5 43)) t) (bvsge (bvshl s (_ bv6 43)) t) (bvsge (bvshl s (_ bv7 43)) t) (bvsge (bvshl s (_ bv8 43)) t) (bvsge (bvshl s (_ bv9 43)) t) (bvsge (bvshl s (_ bv10 43)) t) (bvsge (bvshl s (_ bv11 43)) t) (bvsge (bvshl s (_ bv12 43)) t) (bvsge (bvshl s (_ bv13 43)) t) (bvsge (bvshl s (_ bv14 43)) t) (bvsge (bvshl s (_ bv15 43)) t) (bvsge (bvshl s (_ bv16 43)) t) (bvsge (bvshl s (_ bv17 43)) t) (bvsge (bvshl s (_ bv18 43)) t) (bvsge (bvshl s (_ bv19 43)) t) (bvsge (bvshl s (_ bv20 43)) t) (bvsge (bvshl s (_ bv21 43)) t) (bvsge (bvshl s (_ bv22 43)) t) (bvsge (bvshl s (_ bv23 43)) t) (bvsge (bvshl s (_ bv24 43)) t) (bvsge (bvshl s (_ bv25 43)) t) (bvsge (bvshl s (_ bv26 43)) t) (bvsge (bvshl s (_ bv27 43)) t) (bvsge (bvshl s (_ bv28 43)) t) (bvsge (bvshl s (_ bv29 43)) t) (bvsge (bvshl s (_ bv30 43)) t) (bvsge (bvshl s (_ bv31 43)) t) (bvsge (bvshl s (_ bv32 43)) t) (bvsge (bvshl s (_ bv33 43)) t) (bvsge (bvshl s (_ bv34 43)) t) (bvsge (bvshl s (_ bv35 43)) t) (bvsge (bvshl s (_ bv36 43)) t) (bvsge (bvshl s (_ bv37 43)) t) (bvsge (bvshl s (_ bv38 43)) t) (bvsge (bvshl s (_ bv39 43)) t) (bvsge (bvshl s (_ bv40 43)) t) (bvsge (bvshl s (_ bv41 43)) t) (bvsge (bvshl s (_ bv42 43)) t) (bvsge (bvshl s (_ bv43 43)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 43))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 43))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
