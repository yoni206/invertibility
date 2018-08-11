(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 49))
(declare-fun t () (_ BitVec 49))

(define-fun udivtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) (bvnot (_ bv0 49)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 49)) (b (_ BitVec 49))) (_ BitVec 49)
  (ite (= b (_ bv0 49)) a (bvurem a b))
)
(define-fun min () (_ BitVec 49)
  (bvnot (bvlshr (bvnot (_ bv0 49)) (_ bv1 49)))
)
(define-fun max () (_ BitVec 49)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 49)) (t (_ BitVec 49))) Bool
(or  (bvsge (bvshl s (_ bv0 49)) t) (bvsge (bvshl s (_ bv1 49)) t) (bvsge (bvshl s (_ bv2 49)) t) (bvsge (bvshl s (_ bv3 49)) t) (bvsge (bvshl s (_ bv4 49)) t) (bvsge (bvshl s (_ bv5 49)) t) (bvsge (bvshl s (_ bv6 49)) t) (bvsge (bvshl s (_ bv7 49)) t) (bvsge (bvshl s (_ bv8 49)) t) (bvsge (bvshl s (_ bv9 49)) t) (bvsge (bvshl s (_ bv10 49)) t) (bvsge (bvshl s (_ bv11 49)) t) (bvsge (bvshl s (_ bv12 49)) t) (bvsge (bvshl s (_ bv13 49)) t) (bvsge (bvshl s (_ bv14 49)) t) (bvsge (bvshl s (_ bv15 49)) t) (bvsge (bvshl s (_ bv16 49)) t) (bvsge (bvshl s (_ bv17 49)) t) (bvsge (bvshl s (_ bv18 49)) t) (bvsge (bvshl s (_ bv19 49)) t) (bvsge (bvshl s (_ bv20 49)) t) (bvsge (bvshl s (_ bv21 49)) t) (bvsge (bvshl s (_ bv22 49)) t) (bvsge (bvshl s (_ bv23 49)) t) (bvsge (bvshl s (_ bv24 49)) t) (bvsge (bvshl s (_ bv25 49)) t) (bvsge (bvshl s (_ bv26 49)) t) (bvsge (bvshl s (_ bv27 49)) t) (bvsge (bvshl s (_ bv28 49)) t) (bvsge (bvshl s (_ bv29 49)) t) (bvsge (bvshl s (_ bv30 49)) t) (bvsge (bvshl s (_ bv31 49)) t) (bvsge (bvshl s (_ bv32 49)) t) (bvsge (bvshl s (_ bv33 49)) t) (bvsge (bvshl s (_ bv34 49)) t) (bvsge (bvshl s (_ bv35 49)) t) (bvsge (bvshl s (_ bv36 49)) t) (bvsge (bvshl s (_ bv37 49)) t) (bvsge (bvshl s (_ bv38 49)) t) (bvsge (bvshl s (_ bv39 49)) t) (bvsge (bvshl s (_ bv40 49)) t) (bvsge (bvshl s (_ bv41 49)) t) (bvsge (bvshl s (_ bv42 49)) t) (bvsge (bvshl s (_ bv43 49)) t) (bvsge (bvshl s (_ bv44 49)) t) (bvsge (bvshl s (_ bv45 49)) t) (bvsge (bvshl s (_ bv46 49)) t) (bvsge (bvshl s (_ bv47 49)) t) (bvsge (bvshl s (_ bv48 49)) t) (bvsge (bvshl s (_ bv49 49)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 49))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 49))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
