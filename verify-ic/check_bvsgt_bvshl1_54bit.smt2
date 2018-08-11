(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 54))
(declare-fun t () (_ BitVec 54))

(define-fun udivtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) (bvnot (_ bv0 54)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 54)) (b (_ BitVec 54))) (_ BitVec 54)
  (ite (= b (_ bv0 54)) a (bvurem a b))
)
(define-fun min () (_ BitVec 54)
  (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54)))
)
(define-fun max () (_ BitVec 54)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 54)) (t (_ BitVec 54))) Bool
(or  (bvsgt (bvshl s (_ bv0 54)) t) (bvsgt (bvshl s (_ bv1 54)) t) (bvsgt (bvshl s (_ bv2 54)) t) (bvsgt (bvshl s (_ bv3 54)) t) (bvsgt (bvshl s (_ bv4 54)) t) (bvsgt (bvshl s (_ bv5 54)) t) (bvsgt (bvshl s (_ bv6 54)) t) (bvsgt (bvshl s (_ bv7 54)) t) (bvsgt (bvshl s (_ bv8 54)) t) (bvsgt (bvshl s (_ bv9 54)) t) (bvsgt (bvshl s (_ bv10 54)) t) (bvsgt (bvshl s (_ bv11 54)) t) (bvsgt (bvshl s (_ bv12 54)) t) (bvsgt (bvshl s (_ bv13 54)) t) (bvsgt (bvshl s (_ bv14 54)) t) (bvsgt (bvshl s (_ bv15 54)) t) (bvsgt (bvshl s (_ bv16 54)) t) (bvsgt (bvshl s (_ bv17 54)) t) (bvsgt (bvshl s (_ bv18 54)) t) (bvsgt (bvshl s (_ bv19 54)) t) (bvsgt (bvshl s (_ bv20 54)) t) (bvsgt (bvshl s (_ bv21 54)) t) (bvsgt (bvshl s (_ bv22 54)) t) (bvsgt (bvshl s (_ bv23 54)) t) (bvsgt (bvshl s (_ bv24 54)) t) (bvsgt (bvshl s (_ bv25 54)) t) (bvsgt (bvshl s (_ bv26 54)) t) (bvsgt (bvshl s (_ bv27 54)) t) (bvsgt (bvshl s (_ bv28 54)) t) (bvsgt (bvshl s (_ bv29 54)) t) (bvsgt (bvshl s (_ bv30 54)) t) (bvsgt (bvshl s (_ bv31 54)) t) (bvsgt (bvshl s (_ bv32 54)) t) (bvsgt (bvshl s (_ bv33 54)) t) (bvsgt (bvshl s (_ bv34 54)) t) (bvsgt (bvshl s (_ bv35 54)) t) (bvsgt (bvshl s (_ bv36 54)) t) (bvsgt (bvshl s (_ bv37 54)) t) (bvsgt (bvshl s (_ bv38 54)) t) (bvsgt (bvshl s (_ bv39 54)) t) (bvsgt (bvshl s (_ bv40 54)) t) (bvsgt (bvshl s (_ bv41 54)) t) (bvsgt (bvshl s (_ bv42 54)) t) (bvsgt (bvshl s (_ bv43 54)) t) (bvsgt (bvshl s (_ bv44 54)) t) (bvsgt (bvshl s (_ bv45 54)) t) (bvsgt (bvshl s (_ bv46 54)) t) (bvsgt (bvshl s (_ bv47 54)) t) (bvsgt (bvshl s (_ bv48 54)) t) (bvsgt (bvshl s (_ bv49 54)) t) (bvsgt (bvshl s (_ bv50 54)) t) (bvsgt (bvshl s (_ bv51 54)) t) (bvsgt (bvshl s (_ bv52 54)) t) (bvsgt (bvshl s (_ bv53 54)) t) (bvsgt (bvshl s (_ bv54 54)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 54))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 54))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
