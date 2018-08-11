(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 56))
(declare-fun t () (_ BitVec 56))

(define-fun udivtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) (bvnot (_ bv0 56)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 56)) (b (_ BitVec 56))) (_ BitVec 56)
  (ite (= b (_ bv0 56)) a (bvurem a b))
)
(define-fun min () (_ BitVec 56)
  (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56)))
)
(define-fun max () (_ BitVec 56)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 56)) (t (_ BitVec 56))) Bool
(or  (bvuge (bvshl s (_ bv0 56)) t) (bvuge (bvshl s (_ bv1 56)) t) (bvuge (bvshl s (_ bv2 56)) t) (bvuge (bvshl s (_ bv3 56)) t) (bvuge (bvshl s (_ bv4 56)) t) (bvuge (bvshl s (_ bv5 56)) t) (bvuge (bvshl s (_ bv6 56)) t) (bvuge (bvshl s (_ bv7 56)) t) (bvuge (bvshl s (_ bv8 56)) t) (bvuge (bvshl s (_ bv9 56)) t) (bvuge (bvshl s (_ bv10 56)) t) (bvuge (bvshl s (_ bv11 56)) t) (bvuge (bvshl s (_ bv12 56)) t) (bvuge (bvshl s (_ bv13 56)) t) (bvuge (bvshl s (_ bv14 56)) t) (bvuge (bvshl s (_ bv15 56)) t) (bvuge (bvshl s (_ bv16 56)) t) (bvuge (bvshl s (_ bv17 56)) t) (bvuge (bvshl s (_ bv18 56)) t) (bvuge (bvshl s (_ bv19 56)) t) (bvuge (bvshl s (_ bv20 56)) t) (bvuge (bvshl s (_ bv21 56)) t) (bvuge (bvshl s (_ bv22 56)) t) (bvuge (bvshl s (_ bv23 56)) t) (bvuge (bvshl s (_ bv24 56)) t) (bvuge (bvshl s (_ bv25 56)) t) (bvuge (bvshl s (_ bv26 56)) t) (bvuge (bvshl s (_ bv27 56)) t) (bvuge (bvshl s (_ bv28 56)) t) (bvuge (bvshl s (_ bv29 56)) t) (bvuge (bvshl s (_ bv30 56)) t) (bvuge (bvshl s (_ bv31 56)) t) (bvuge (bvshl s (_ bv32 56)) t) (bvuge (bvshl s (_ bv33 56)) t) (bvuge (bvshl s (_ bv34 56)) t) (bvuge (bvshl s (_ bv35 56)) t) (bvuge (bvshl s (_ bv36 56)) t) (bvuge (bvshl s (_ bv37 56)) t) (bvuge (bvshl s (_ bv38 56)) t) (bvuge (bvshl s (_ bv39 56)) t) (bvuge (bvshl s (_ bv40 56)) t) (bvuge (bvshl s (_ bv41 56)) t) (bvuge (bvshl s (_ bv42 56)) t) (bvuge (bvshl s (_ bv43 56)) t) (bvuge (bvshl s (_ bv44 56)) t) (bvuge (bvshl s (_ bv45 56)) t) (bvuge (bvshl s (_ bv46 56)) t) (bvuge (bvshl s (_ bv47 56)) t) (bvuge (bvshl s (_ bv48 56)) t) (bvuge (bvshl s (_ bv49 56)) t) (bvuge (bvshl s (_ bv50 56)) t) (bvuge (bvshl s (_ bv51 56)) t) (bvuge (bvshl s (_ bv52 56)) t) (bvuge (bvshl s (_ bv53 56)) t) (bvuge (bvshl s (_ bv54 56)) t) (bvuge (bvshl s (_ bv55 56)) t) (bvuge (bvshl s (_ bv56 56)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 56))) (bvuge (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 56))) (bvuge (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
