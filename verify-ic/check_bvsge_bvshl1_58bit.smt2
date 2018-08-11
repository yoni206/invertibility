(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 58))
(declare-fun t () (_ BitVec 58))

(define-fun udivtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) (bvnot (_ bv0 58)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 58)) (b (_ BitVec 58))) (_ BitVec 58)
  (ite (= b (_ bv0 58)) a (bvurem a b))
)
(define-fun min () (_ BitVec 58)
  (bvnot (bvlshr (bvnot (_ bv0 58)) (_ bv1 58)))
)
(define-fun max () (_ BitVec 58)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 58)) (t (_ BitVec 58))) Bool
(or  (bvsge (bvshl s (_ bv0 58)) t) (bvsge (bvshl s (_ bv1 58)) t) (bvsge (bvshl s (_ bv2 58)) t) (bvsge (bvshl s (_ bv3 58)) t) (bvsge (bvshl s (_ bv4 58)) t) (bvsge (bvshl s (_ bv5 58)) t) (bvsge (bvshl s (_ bv6 58)) t) (bvsge (bvshl s (_ bv7 58)) t) (bvsge (bvshl s (_ bv8 58)) t) (bvsge (bvshl s (_ bv9 58)) t) (bvsge (bvshl s (_ bv10 58)) t) (bvsge (bvshl s (_ bv11 58)) t) (bvsge (bvshl s (_ bv12 58)) t) (bvsge (bvshl s (_ bv13 58)) t) (bvsge (bvshl s (_ bv14 58)) t) (bvsge (bvshl s (_ bv15 58)) t) (bvsge (bvshl s (_ bv16 58)) t) (bvsge (bvshl s (_ bv17 58)) t) (bvsge (bvshl s (_ bv18 58)) t) (bvsge (bvshl s (_ bv19 58)) t) (bvsge (bvshl s (_ bv20 58)) t) (bvsge (bvshl s (_ bv21 58)) t) (bvsge (bvshl s (_ bv22 58)) t) (bvsge (bvshl s (_ bv23 58)) t) (bvsge (bvshl s (_ bv24 58)) t) (bvsge (bvshl s (_ bv25 58)) t) (bvsge (bvshl s (_ bv26 58)) t) (bvsge (bvshl s (_ bv27 58)) t) (bvsge (bvshl s (_ bv28 58)) t) (bvsge (bvshl s (_ bv29 58)) t) (bvsge (bvshl s (_ bv30 58)) t) (bvsge (bvshl s (_ bv31 58)) t) (bvsge (bvshl s (_ bv32 58)) t) (bvsge (bvshl s (_ bv33 58)) t) (bvsge (bvshl s (_ bv34 58)) t) (bvsge (bvshl s (_ bv35 58)) t) (bvsge (bvshl s (_ bv36 58)) t) (bvsge (bvshl s (_ bv37 58)) t) (bvsge (bvshl s (_ bv38 58)) t) (bvsge (bvshl s (_ bv39 58)) t) (bvsge (bvshl s (_ bv40 58)) t) (bvsge (bvshl s (_ bv41 58)) t) (bvsge (bvshl s (_ bv42 58)) t) (bvsge (bvshl s (_ bv43 58)) t) (bvsge (bvshl s (_ bv44 58)) t) (bvsge (bvshl s (_ bv45 58)) t) (bvsge (bvshl s (_ bv46 58)) t) (bvsge (bvshl s (_ bv47 58)) t) (bvsge (bvshl s (_ bv48 58)) t) (bvsge (bvshl s (_ bv49 58)) t) (bvsge (bvshl s (_ bv50 58)) t) (bvsge (bvshl s (_ bv51 58)) t) (bvsge (bvshl s (_ bv52 58)) t) (bvsge (bvshl s (_ bv53 58)) t) (bvsge (bvshl s (_ bv54 58)) t) (bvsge (bvshl s (_ bv55 58)) t) (bvsge (bvshl s (_ bv56 58)) t) (bvsge (bvshl s (_ bv57 58)) t) (bvsge (bvshl s (_ bv58 58)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 58))) (bvsge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 58))) (bvsge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
