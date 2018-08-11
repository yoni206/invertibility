(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 59))
(declare-fun t () (_ BitVec 59))

(define-fun udivtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) (bvnot (_ bv0 59)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 59)) (b (_ BitVec 59))) (_ BitVec 59)
  (ite (= b (_ bv0 59)) a (bvurem a b))
)
(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 59)) (t (_ BitVec 59))) Bool
(or  (bvsge (bvshl s (_ bv0 59)) t) (bvsge (bvshl s (_ bv1 59)) t) (bvsge (bvshl s (_ bv2 59)) t) (bvsge (bvshl s (_ bv3 59)) t) (bvsge (bvshl s (_ bv4 59)) t) (bvsge (bvshl s (_ bv5 59)) t) (bvsge (bvshl s (_ bv6 59)) t) (bvsge (bvshl s (_ bv7 59)) t) (bvsge (bvshl s (_ bv8 59)) t) (bvsge (bvshl s (_ bv9 59)) t) (bvsge (bvshl s (_ bv10 59)) t) (bvsge (bvshl s (_ bv11 59)) t) (bvsge (bvshl s (_ bv12 59)) t) (bvsge (bvshl s (_ bv13 59)) t) (bvsge (bvshl s (_ bv14 59)) t) (bvsge (bvshl s (_ bv15 59)) t) (bvsge (bvshl s (_ bv16 59)) t) (bvsge (bvshl s (_ bv17 59)) t) (bvsge (bvshl s (_ bv18 59)) t) (bvsge (bvshl s (_ bv19 59)) t) (bvsge (bvshl s (_ bv20 59)) t) (bvsge (bvshl s (_ bv21 59)) t) (bvsge (bvshl s (_ bv22 59)) t) (bvsge (bvshl s (_ bv23 59)) t) (bvsge (bvshl s (_ bv24 59)) t) (bvsge (bvshl s (_ bv25 59)) t) (bvsge (bvshl s (_ bv26 59)) t) (bvsge (bvshl s (_ bv27 59)) t) (bvsge (bvshl s (_ bv28 59)) t) (bvsge (bvshl s (_ bv29 59)) t) (bvsge (bvshl s (_ bv30 59)) t) (bvsge (bvshl s (_ bv31 59)) t) (bvsge (bvshl s (_ bv32 59)) t) (bvsge (bvshl s (_ bv33 59)) t) (bvsge (bvshl s (_ bv34 59)) t) (bvsge (bvshl s (_ bv35 59)) t) (bvsge (bvshl s (_ bv36 59)) t) (bvsge (bvshl s (_ bv37 59)) t) (bvsge (bvshl s (_ bv38 59)) t) (bvsge (bvshl s (_ bv39 59)) t) (bvsge (bvshl s (_ bv40 59)) t) (bvsge (bvshl s (_ bv41 59)) t) (bvsge (bvshl s (_ bv42 59)) t) (bvsge (bvshl s (_ bv43 59)) t) (bvsge (bvshl s (_ bv44 59)) t) (bvsge (bvshl s (_ bv45 59)) t) (bvsge (bvshl s (_ bv46 59)) t) (bvsge (bvshl s (_ bv47 59)) t) (bvsge (bvshl s (_ bv48 59)) t) (bvsge (bvshl s (_ bv49 59)) t) (bvsge (bvshl s (_ bv50 59)) t) (bvsge (bvshl s (_ bv51 59)) t) (bvsge (bvshl s (_ bv52 59)) t) (bvsge (bvshl s (_ bv53 59)) t) (bvsge (bvshl s (_ bv54 59)) t) (bvsge (bvshl s (_ bv55 59)) t) (bvsge (bvshl s (_ bv56 59)) t) (bvsge (bvshl s (_ bv57 59)) t) (bvsge (bvshl s (_ bv58 59)) t) (bvsge (bvshl s (_ bv59 59)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 59))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 59))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
