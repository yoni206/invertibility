(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun t () (_ BitVec 63))

(define-fun udivtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) (bvnot (_ bv0 63)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 63)) (b (_ BitVec 63))) (_ BitVec 63)
  (ite (= b (_ bv0 63)) a (bvurem a b))
)
(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 63)) (t (_ BitVec 63))) Bool
(or  (= (bvshl s (_ bv0 63)) t) (= (bvshl s (_ bv1 63)) t) (= (bvshl s (_ bv2 63)) t) (= (bvshl s (_ bv3 63)) t) (= (bvshl s (_ bv4 63)) t) (= (bvshl s (_ bv5 63)) t) (= (bvshl s (_ bv6 63)) t) (= (bvshl s (_ bv7 63)) t) (= (bvshl s (_ bv8 63)) t) (= (bvshl s (_ bv9 63)) t) (= (bvshl s (_ bv10 63)) t) (= (bvshl s (_ bv11 63)) t) (= (bvshl s (_ bv12 63)) t) (= (bvshl s (_ bv13 63)) t) (= (bvshl s (_ bv14 63)) t) (= (bvshl s (_ bv15 63)) t) (= (bvshl s (_ bv16 63)) t) (= (bvshl s (_ bv17 63)) t) (= (bvshl s (_ bv18 63)) t) (= (bvshl s (_ bv19 63)) t) (= (bvshl s (_ bv20 63)) t) (= (bvshl s (_ bv21 63)) t) (= (bvshl s (_ bv22 63)) t) (= (bvshl s (_ bv23 63)) t) (= (bvshl s (_ bv24 63)) t) (= (bvshl s (_ bv25 63)) t) (= (bvshl s (_ bv26 63)) t) (= (bvshl s (_ bv27 63)) t) (= (bvshl s (_ bv28 63)) t) (= (bvshl s (_ bv29 63)) t) (= (bvshl s (_ bv30 63)) t) (= (bvshl s (_ bv31 63)) t) (= (bvshl s (_ bv32 63)) t) (= (bvshl s (_ bv33 63)) t) (= (bvshl s (_ bv34 63)) t) (= (bvshl s (_ bv35 63)) t) (= (bvshl s (_ bv36 63)) t) (= (bvshl s (_ bv37 63)) t) (= (bvshl s (_ bv38 63)) t) (= (bvshl s (_ bv39 63)) t) (= (bvshl s (_ bv40 63)) t) (= (bvshl s (_ bv41 63)) t) (= (bvshl s (_ bv42 63)) t) (= (bvshl s (_ bv43 63)) t) (= (bvshl s (_ bv44 63)) t) (= (bvshl s (_ bv45 63)) t) (= (bvshl s (_ bv46 63)) t) (= (bvshl s (_ bv47 63)) t) (= (bvshl s (_ bv48 63)) t) (= (bvshl s (_ bv49 63)) t) (= (bvshl s (_ bv50 63)) t) (= (bvshl s (_ bv51 63)) t) (= (bvshl s (_ bv52 63)) t) (= (bvshl s (_ bv53 63)) t) (= (bvshl s (_ bv54 63)) t) (= (bvshl s (_ bv55 63)) t) (= (bvshl s (_ bv56 63)) t) (= (bvshl s (_ bv57 63)) t) (= (bvshl s (_ bv58 63)) t) (= (bvshl s (_ bv59 63)) t) (= (bvshl s (_ bv60 63)) t) (= (bvshl s (_ bv61 63)) t) (= (bvshl s (_ bv62 63)) t) (= (bvshl s (_ bv63 63)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 63))) (= (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 63))) (= (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
