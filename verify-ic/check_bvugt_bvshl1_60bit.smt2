(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 60))
(declare-fun t () (_ BitVec 60))

(define-fun udivtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) (bvnot (_ bv0 60)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 60)) (b (_ BitVec 60))) (_ BitVec 60)
  (ite (= b (_ bv0 60)) a (bvurem a b))
)
(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 60)) (t (_ BitVec 60))) Bool
(or  (bvugt (bvshl s (_ bv0 60)) t) (bvugt (bvshl s (_ bv1 60)) t) (bvugt (bvshl s (_ bv2 60)) t) (bvugt (bvshl s (_ bv3 60)) t) (bvugt (bvshl s (_ bv4 60)) t) (bvugt (bvshl s (_ bv5 60)) t) (bvugt (bvshl s (_ bv6 60)) t) (bvugt (bvshl s (_ bv7 60)) t) (bvugt (bvshl s (_ bv8 60)) t) (bvugt (bvshl s (_ bv9 60)) t) (bvugt (bvshl s (_ bv10 60)) t) (bvugt (bvshl s (_ bv11 60)) t) (bvugt (bvshl s (_ bv12 60)) t) (bvugt (bvshl s (_ bv13 60)) t) (bvugt (bvshl s (_ bv14 60)) t) (bvugt (bvshl s (_ bv15 60)) t) (bvugt (bvshl s (_ bv16 60)) t) (bvugt (bvshl s (_ bv17 60)) t) (bvugt (bvshl s (_ bv18 60)) t) (bvugt (bvshl s (_ bv19 60)) t) (bvugt (bvshl s (_ bv20 60)) t) (bvugt (bvshl s (_ bv21 60)) t) (bvugt (bvshl s (_ bv22 60)) t) (bvugt (bvshl s (_ bv23 60)) t) (bvugt (bvshl s (_ bv24 60)) t) (bvugt (bvshl s (_ bv25 60)) t) (bvugt (bvshl s (_ bv26 60)) t) (bvugt (bvshl s (_ bv27 60)) t) (bvugt (bvshl s (_ bv28 60)) t) (bvugt (bvshl s (_ bv29 60)) t) (bvugt (bvshl s (_ bv30 60)) t) (bvugt (bvshl s (_ bv31 60)) t) (bvugt (bvshl s (_ bv32 60)) t) (bvugt (bvshl s (_ bv33 60)) t) (bvugt (bvshl s (_ bv34 60)) t) (bvugt (bvshl s (_ bv35 60)) t) (bvugt (bvshl s (_ bv36 60)) t) (bvugt (bvshl s (_ bv37 60)) t) (bvugt (bvshl s (_ bv38 60)) t) (bvugt (bvshl s (_ bv39 60)) t) (bvugt (bvshl s (_ bv40 60)) t) (bvugt (bvshl s (_ bv41 60)) t) (bvugt (bvshl s (_ bv42 60)) t) (bvugt (bvshl s (_ bv43 60)) t) (bvugt (bvshl s (_ bv44 60)) t) (bvugt (bvshl s (_ bv45 60)) t) (bvugt (bvshl s (_ bv46 60)) t) (bvugt (bvshl s (_ bv47 60)) t) (bvugt (bvshl s (_ bv48 60)) t) (bvugt (bvshl s (_ bv49 60)) t) (bvugt (bvshl s (_ bv50 60)) t) (bvugt (bvshl s (_ bv51 60)) t) (bvugt (bvshl s (_ bv52 60)) t) (bvugt (bvshl s (_ bv53 60)) t) (bvugt (bvshl s (_ bv54 60)) t) (bvugt (bvshl s (_ bv55 60)) t) (bvugt (bvshl s (_ bv56 60)) t) (bvugt (bvshl s (_ bv57 60)) t) (bvugt (bvshl s (_ bv58 60)) t) (bvugt (bvshl s (_ bv59 60)) t) (bvugt (bvshl s (_ bv60 60)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 60))) (bvugt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 60))) (bvugt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
