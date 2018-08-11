(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 48))
(declare-fun t () (_ BitVec 48))

(define-fun udivtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) (bvnot (_ bv0 48)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 48)) (b (_ BitVec 48))) (_ BitVec 48)
  (ite (= b (_ bv0 48)) a (bvurem a b))
)
(define-fun min () (_ BitVec 48)
  (bvnot (bvlshr (bvnot (_ bv0 48)) (_ bv1 48)))
)
(define-fun max () (_ BitVec 48)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 48)) (t (_ BitVec 48))) Bool
(or  (bvsgt (bvshl s (_ bv0 48)) t) (bvsgt (bvshl s (_ bv1 48)) t) (bvsgt (bvshl s (_ bv2 48)) t) (bvsgt (bvshl s (_ bv3 48)) t) (bvsgt (bvshl s (_ bv4 48)) t) (bvsgt (bvshl s (_ bv5 48)) t) (bvsgt (bvshl s (_ bv6 48)) t) (bvsgt (bvshl s (_ bv7 48)) t) (bvsgt (bvshl s (_ bv8 48)) t) (bvsgt (bvshl s (_ bv9 48)) t) (bvsgt (bvshl s (_ bv10 48)) t) (bvsgt (bvshl s (_ bv11 48)) t) (bvsgt (bvshl s (_ bv12 48)) t) (bvsgt (bvshl s (_ bv13 48)) t) (bvsgt (bvshl s (_ bv14 48)) t) (bvsgt (bvshl s (_ bv15 48)) t) (bvsgt (bvshl s (_ bv16 48)) t) (bvsgt (bvshl s (_ bv17 48)) t) (bvsgt (bvshl s (_ bv18 48)) t) (bvsgt (bvshl s (_ bv19 48)) t) (bvsgt (bvshl s (_ bv20 48)) t) (bvsgt (bvshl s (_ bv21 48)) t) (bvsgt (bvshl s (_ bv22 48)) t) (bvsgt (bvshl s (_ bv23 48)) t) (bvsgt (bvshl s (_ bv24 48)) t) (bvsgt (bvshl s (_ bv25 48)) t) (bvsgt (bvshl s (_ bv26 48)) t) (bvsgt (bvshl s (_ bv27 48)) t) (bvsgt (bvshl s (_ bv28 48)) t) (bvsgt (bvshl s (_ bv29 48)) t) (bvsgt (bvshl s (_ bv30 48)) t) (bvsgt (bvshl s (_ bv31 48)) t) (bvsgt (bvshl s (_ bv32 48)) t) (bvsgt (bvshl s (_ bv33 48)) t) (bvsgt (bvshl s (_ bv34 48)) t) (bvsgt (bvshl s (_ bv35 48)) t) (bvsgt (bvshl s (_ bv36 48)) t) (bvsgt (bvshl s (_ bv37 48)) t) (bvsgt (bvshl s (_ bv38 48)) t) (bvsgt (bvshl s (_ bv39 48)) t) (bvsgt (bvshl s (_ bv40 48)) t) (bvsgt (bvshl s (_ bv41 48)) t) (bvsgt (bvshl s (_ bv42 48)) t) (bvsgt (bvshl s (_ bv43 48)) t) (bvsgt (bvshl s (_ bv44 48)) t) (bvsgt (bvshl s (_ bv45 48)) t) (bvsgt (bvshl s (_ bv46 48)) t) (bvsgt (bvshl s (_ bv47 48)) t) (bvsgt (bvshl s (_ bv48 48)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 48))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 48))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
