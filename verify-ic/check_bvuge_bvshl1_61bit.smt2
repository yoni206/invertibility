(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 61))
(declare-fun t () (_ BitVec 61))

(define-fun udivtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) (bvnot (_ bv0 61)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 61)) (b (_ BitVec 61))) (_ BitVec 61)
  (ite (= b (_ bv0 61)) a (bvurem a b))
)
(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 61)) (t (_ BitVec 61))) Bool
(or  (bvuge (bvshl s (_ bv0 61)) t) (bvuge (bvshl s (_ bv1 61)) t) (bvuge (bvshl s (_ bv2 61)) t) (bvuge (bvshl s (_ bv3 61)) t) (bvuge (bvshl s (_ bv4 61)) t) (bvuge (bvshl s (_ bv5 61)) t) (bvuge (bvshl s (_ bv6 61)) t) (bvuge (bvshl s (_ bv7 61)) t) (bvuge (bvshl s (_ bv8 61)) t) (bvuge (bvshl s (_ bv9 61)) t) (bvuge (bvshl s (_ bv10 61)) t) (bvuge (bvshl s (_ bv11 61)) t) (bvuge (bvshl s (_ bv12 61)) t) (bvuge (bvshl s (_ bv13 61)) t) (bvuge (bvshl s (_ bv14 61)) t) (bvuge (bvshl s (_ bv15 61)) t) (bvuge (bvshl s (_ bv16 61)) t) (bvuge (bvshl s (_ bv17 61)) t) (bvuge (bvshl s (_ bv18 61)) t) (bvuge (bvshl s (_ bv19 61)) t) (bvuge (bvshl s (_ bv20 61)) t) (bvuge (bvshl s (_ bv21 61)) t) (bvuge (bvshl s (_ bv22 61)) t) (bvuge (bvshl s (_ bv23 61)) t) (bvuge (bvshl s (_ bv24 61)) t) (bvuge (bvshl s (_ bv25 61)) t) (bvuge (bvshl s (_ bv26 61)) t) (bvuge (bvshl s (_ bv27 61)) t) (bvuge (bvshl s (_ bv28 61)) t) (bvuge (bvshl s (_ bv29 61)) t) (bvuge (bvshl s (_ bv30 61)) t) (bvuge (bvshl s (_ bv31 61)) t) (bvuge (bvshl s (_ bv32 61)) t) (bvuge (bvshl s (_ bv33 61)) t) (bvuge (bvshl s (_ bv34 61)) t) (bvuge (bvshl s (_ bv35 61)) t) (bvuge (bvshl s (_ bv36 61)) t) (bvuge (bvshl s (_ bv37 61)) t) (bvuge (bvshl s (_ bv38 61)) t) (bvuge (bvshl s (_ bv39 61)) t) (bvuge (bvshl s (_ bv40 61)) t) (bvuge (bvshl s (_ bv41 61)) t) (bvuge (bvshl s (_ bv42 61)) t) (bvuge (bvshl s (_ bv43 61)) t) (bvuge (bvshl s (_ bv44 61)) t) (bvuge (bvshl s (_ bv45 61)) t) (bvuge (bvshl s (_ bv46 61)) t) (bvuge (bvshl s (_ bv47 61)) t) (bvuge (bvshl s (_ bv48 61)) t) (bvuge (bvshl s (_ bv49 61)) t) (bvuge (bvshl s (_ bv50 61)) t) (bvuge (bvshl s (_ bv51 61)) t) (bvuge (bvshl s (_ bv52 61)) t) (bvuge (bvshl s (_ bv53 61)) t) (bvuge (bvshl s (_ bv54 61)) t) (bvuge (bvshl s (_ bv55 61)) t) (bvuge (bvshl s (_ bv56 61)) t) (bvuge (bvshl s (_ bv57 61)) t) (bvuge (bvshl s (_ bv58 61)) t) (bvuge (bvshl s (_ bv59 61)) t) (bvuge (bvshl s (_ bv60 61)) t) (bvuge (bvshl s (_ bv61 61)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 61))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 61))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
