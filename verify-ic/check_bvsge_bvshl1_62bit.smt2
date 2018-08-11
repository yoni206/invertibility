(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 62))
(declare-fun t () (_ BitVec 62))

(define-fun udivtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) (bvnot (_ bv0 62)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 62)) (b (_ BitVec 62))) (_ BitVec 62)
  (ite (= b (_ bv0 62)) a (bvurem a b))
)
(define-fun min () (_ BitVec 62)
  (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62)))
)
(define-fun max () (_ BitVec 62)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 62)) (t (_ BitVec 62))) Bool
(or  (bvsge (bvshl s (_ bv0 62)) t) (bvsge (bvshl s (_ bv1 62)) t) (bvsge (bvshl s (_ bv2 62)) t) (bvsge (bvshl s (_ bv3 62)) t) (bvsge (bvshl s (_ bv4 62)) t) (bvsge (bvshl s (_ bv5 62)) t) (bvsge (bvshl s (_ bv6 62)) t) (bvsge (bvshl s (_ bv7 62)) t) (bvsge (bvshl s (_ bv8 62)) t) (bvsge (bvshl s (_ bv9 62)) t) (bvsge (bvshl s (_ bv10 62)) t) (bvsge (bvshl s (_ bv11 62)) t) (bvsge (bvshl s (_ bv12 62)) t) (bvsge (bvshl s (_ bv13 62)) t) (bvsge (bvshl s (_ bv14 62)) t) (bvsge (bvshl s (_ bv15 62)) t) (bvsge (bvshl s (_ bv16 62)) t) (bvsge (bvshl s (_ bv17 62)) t) (bvsge (bvshl s (_ bv18 62)) t) (bvsge (bvshl s (_ bv19 62)) t) (bvsge (bvshl s (_ bv20 62)) t) (bvsge (bvshl s (_ bv21 62)) t) (bvsge (bvshl s (_ bv22 62)) t) (bvsge (bvshl s (_ bv23 62)) t) (bvsge (bvshl s (_ bv24 62)) t) (bvsge (bvshl s (_ bv25 62)) t) (bvsge (bvshl s (_ bv26 62)) t) (bvsge (bvshl s (_ bv27 62)) t) (bvsge (bvshl s (_ bv28 62)) t) (bvsge (bvshl s (_ bv29 62)) t) (bvsge (bvshl s (_ bv30 62)) t) (bvsge (bvshl s (_ bv31 62)) t) (bvsge (bvshl s (_ bv32 62)) t) (bvsge (bvshl s (_ bv33 62)) t) (bvsge (bvshl s (_ bv34 62)) t) (bvsge (bvshl s (_ bv35 62)) t) (bvsge (bvshl s (_ bv36 62)) t) (bvsge (bvshl s (_ bv37 62)) t) (bvsge (bvshl s (_ bv38 62)) t) (bvsge (bvshl s (_ bv39 62)) t) (bvsge (bvshl s (_ bv40 62)) t) (bvsge (bvshl s (_ bv41 62)) t) (bvsge (bvshl s (_ bv42 62)) t) (bvsge (bvshl s (_ bv43 62)) t) (bvsge (bvshl s (_ bv44 62)) t) (bvsge (bvshl s (_ bv45 62)) t) (bvsge (bvshl s (_ bv46 62)) t) (bvsge (bvshl s (_ bv47 62)) t) (bvsge (bvshl s (_ bv48 62)) t) (bvsge (bvshl s (_ bv49 62)) t) (bvsge (bvshl s (_ bv50 62)) t) (bvsge (bvshl s (_ bv51 62)) t) (bvsge (bvshl s (_ bv52 62)) t) (bvsge (bvshl s (_ bv53 62)) t) (bvsge (bvshl s (_ bv54 62)) t) (bvsge (bvshl s (_ bv55 62)) t) (bvsge (bvshl s (_ bv56 62)) t) (bvsge (bvshl s (_ bv57 62)) t) (bvsge (bvshl s (_ bv58 62)) t) (bvsge (bvshl s (_ bv59 62)) t) (bvsge (bvshl s (_ bv60 62)) t) (bvsge (bvshl s (_ bv61 62)) t) (bvsge (bvshl s (_ bv62 62)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 62))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 62))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
