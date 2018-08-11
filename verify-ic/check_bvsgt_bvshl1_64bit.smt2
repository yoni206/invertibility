(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 64))
(declare-fun t () (_ BitVec 64))

(define-fun udivtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) (bvnot (_ bv0 64)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 64)) (b (_ BitVec 64))) (_ BitVec 64)
  (ite (= b (_ bv0 64)) a (bvurem a b))
)
(define-fun min () (_ BitVec 64)
  (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64)))
)
(define-fun max () (_ BitVec 64)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 64)) (t (_ BitVec 64))) Bool
(or  (bvsgt (bvshl s (_ bv0 64)) t) (bvsgt (bvshl s (_ bv1 64)) t) (bvsgt (bvshl s (_ bv2 64)) t) (bvsgt (bvshl s (_ bv3 64)) t) (bvsgt (bvshl s (_ bv4 64)) t) (bvsgt (bvshl s (_ bv5 64)) t) (bvsgt (bvshl s (_ bv6 64)) t) (bvsgt (bvshl s (_ bv7 64)) t) (bvsgt (bvshl s (_ bv8 64)) t) (bvsgt (bvshl s (_ bv9 64)) t) (bvsgt (bvshl s (_ bv10 64)) t) (bvsgt (bvshl s (_ bv11 64)) t) (bvsgt (bvshl s (_ bv12 64)) t) (bvsgt (bvshl s (_ bv13 64)) t) (bvsgt (bvshl s (_ bv14 64)) t) (bvsgt (bvshl s (_ bv15 64)) t) (bvsgt (bvshl s (_ bv16 64)) t) (bvsgt (bvshl s (_ bv17 64)) t) (bvsgt (bvshl s (_ bv18 64)) t) (bvsgt (bvshl s (_ bv19 64)) t) (bvsgt (bvshl s (_ bv20 64)) t) (bvsgt (bvshl s (_ bv21 64)) t) (bvsgt (bvshl s (_ bv22 64)) t) (bvsgt (bvshl s (_ bv23 64)) t) (bvsgt (bvshl s (_ bv24 64)) t) (bvsgt (bvshl s (_ bv25 64)) t) (bvsgt (bvshl s (_ bv26 64)) t) (bvsgt (bvshl s (_ bv27 64)) t) (bvsgt (bvshl s (_ bv28 64)) t) (bvsgt (bvshl s (_ bv29 64)) t) (bvsgt (bvshl s (_ bv30 64)) t) (bvsgt (bvshl s (_ bv31 64)) t) (bvsgt (bvshl s (_ bv32 64)) t) (bvsgt (bvshl s (_ bv33 64)) t) (bvsgt (bvshl s (_ bv34 64)) t) (bvsgt (bvshl s (_ bv35 64)) t) (bvsgt (bvshl s (_ bv36 64)) t) (bvsgt (bvshl s (_ bv37 64)) t) (bvsgt (bvshl s (_ bv38 64)) t) (bvsgt (bvshl s (_ bv39 64)) t) (bvsgt (bvshl s (_ bv40 64)) t) (bvsgt (bvshl s (_ bv41 64)) t) (bvsgt (bvshl s (_ bv42 64)) t) (bvsgt (bvshl s (_ bv43 64)) t) (bvsgt (bvshl s (_ bv44 64)) t) (bvsgt (bvshl s (_ bv45 64)) t) (bvsgt (bvshl s (_ bv46 64)) t) (bvsgt (bvshl s (_ bv47 64)) t) (bvsgt (bvshl s (_ bv48 64)) t) (bvsgt (bvshl s (_ bv49 64)) t) (bvsgt (bvshl s (_ bv50 64)) t) (bvsgt (bvshl s (_ bv51 64)) t) (bvsgt (bvshl s (_ bv52 64)) t) (bvsgt (bvshl s (_ bv53 64)) t) (bvsgt (bvshl s (_ bv54 64)) t) (bvsgt (bvshl s (_ bv55 64)) t) (bvsgt (bvshl s (_ bv56 64)) t) (bvsgt (bvshl s (_ bv57 64)) t) (bvsgt (bvshl s (_ bv58 64)) t) (bvsgt (bvshl s (_ bv59 64)) t) (bvsgt (bvshl s (_ bv60 64)) t) (bvsgt (bvshl s (_ bv61 64)) t) (bvsgt (bvshl s (_ bv62 64)) t) (bvsgt (bvshl s (_ bv63 64)) t) (bvsgt (bvshl s (_ bv64 64)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 64))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 64))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
