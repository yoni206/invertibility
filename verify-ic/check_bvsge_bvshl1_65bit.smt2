(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 65))
(declare-fun t () (_ BitVec 65))

(define-fun udivtotal ((a (_ BitVec 65)) (b (_ BitVec 65))) (_ BitVec 65)
  (ite (= b (_ bv0 65)) (bvnot (_ bv0 65)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 65)) (b (_ BitVec 65))) (_ BitVec 65)
  (ite (= b (_ bv0 65)) a (bvurem a b))
)
(define-fun min () (_ BitVec 65)
  (bvnot (bvlshr (bvnot (_ bv0 65)) (_ bv1 65)))
)
(define-fun max () (_ BitVec 65)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 65)) (t (_ BitVec 65))) Bool
(or  (bvsge (bvshl s (_ bv0 65)) t) (bvsge (bvshl s (_ bv1 65)) t) (bvsge (bvshl s (_ bv2 65)) t) (bvsge (bvshl s (_ bv3 65)) t) (bvsge (bvshl s (_ bv4 65)) t) (bvsge (bvshl s (_ bv5 65)) t) (bvsge (bvshl s (_ bv6 65)) t) (bvsge (bvshl s (_ bv7 65)) t) (bvsge (bvshl s (_ bv8 65)) t) (bvsge (bvshl s (_ bv9 65)) t) (bvsge (bvshl s (_ bv10 65)) t) (bvsge (bvshl s (_ bv11 65)) t) (bvsge (bvshl s (_ bv12 65)) t) (bvsge (bvshl s (_ bv13 65)) t) (bvsge (bvshl s (_ bv14 65)) t) (bvsge (bvshl s (_ bv15 65)) t) (bvsge (bvshl s (_ bv16 65)) t) (bvsge (bvshl s (_ bv17 65)) t) (bvsge (bvshl s (_ bv18 65)) t) (bvsge (bvshl s (_ bv19 65)) t) (bvsge (bvshl s (_ bv20 65)) t) (bvsge (bvshl s (_ bv21 65)) t) (bvsge (bvshl s (_ bv22 65)) t) (bvsge (bvshl s (_ bv23 65)) t) (bvsge (bvshl s (_ bv24 65)) t) (bvsge (bvshl s (_ bv25 65)) t) (bvsge (bvshl s (_ bv26 65)) t) (bvsge (bvshl s (_ bv27 65)) t) (bvsge (bvshl s (_ bv28 65)) t) (bvsge (bvshl s (_ bv29 65)) t) (bvsge (bvshl s (_ bv30 65)) t) (bvsge (bvshl s (_ bv31 65)) t) (bvsge (bvshl s (_ bv32 65)) t) (bvsge (bvshl s (_ bv33 65)) t) (bvsge (bvshl s (_ bv34 65)) t) (bvsge (bvshl s (_ bv35 65)) t) (bvsge (bvshl s (_ bv36 65)) t) (bvsge (bvshl s (_ bv37 65)) t) (bvsge (bvshl s (_ bv38 65)) t) (bvsge (bvshl s (_ bv39 65)) t) (bvsge (bvshl s (_ bv40 65)) t) (bvsge (bvshl s (_ bv41 65)) t) (bvsge (bvshl s (_ bv42 65)) t) (bvsge (bvshl s (_ bv43 65)) t) (bvsge (bvshl s (_ bv44 65)) t) (bvsge (bvshl s (_ bv45 65)) t) (bvsge (bvshl s (_ bv46 65)) t) (bvsge (bvshl s (_ bv47 65)) t) (bvsge (bvshl s (_ bv48 65)) t) (bvsge (bvshl s (_ bv49 65)) t) (bvsge (bvshl s (_ bv50 65)) t) (bvsge (bvshl s (_ bv51 65)) t) (bvsge (bvshl s (_ bv52 65)) t) (bvsge (bvshl s (_ bv53 65)) t) (bvsge (bvshl s (_ bv54 65)) t) (bvsge (bvshl s (_ bv55 65)) t) (bvsge (bvshl s (_ bv56 65)) t) (bvsge (bvshl s (_ bv57 65)) t) (bvsge (bvshl s (_ bv58 65)) t) (bvsge (bvshl s (_ bv59 65)) t) (bvsge (bvshl s (_ bv60 65)) t) (bvsge (bvshl s (_ bv61 65)) t) (bvsge (bvshl s (_ bv62 65)) t) (bvsge (bvshl s (_ bv63 65)) t) (bvsge (bvshl s (_ bv64 65)) t) (bvsge (bvshl s (_ bv65 65)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 65))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 65))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
