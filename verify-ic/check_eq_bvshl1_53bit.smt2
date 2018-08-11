(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 53))
(declare-fun t () (_ BitVec 53))

(define-fun udivtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) (bvnot (_ bv0 53)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 53)) (b (_ BitVec 53))) (_ BitVec 53)
  (ite (= b (_ bv0 53)) a (bvurem a b))
)
(define-fun min () (_ BitVec 53)
  (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53)))
)
(define-fun max () (_ BitVec 53)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 53)) (t (_ BitVec 53))) Bool
(or  (= (bvshl s (_ bv0 53)) t) (= (bvshl s (_ bv1 53)) t) (= (bvshl s (_ bv2 53)) t) (= (bvshl s (_ bv3 53)) t) (= (bvshl s (_ bv4 53)) t) (= (bvshl s (_ bv5 53)) t) (= (bvshl s (_ bv6 53)) t) (= (bvshl s (_ bv7 53)) t) (= (bvshl s (_ bv8 53)) t) (= (bvshl s (_ bv9 53)) t) (= (bvshl s (_ bv10 53)) t) (= (bvshl s (_ bv11 53)) t) (= (bvshl s (_ bv12 53)) t) (= (bvshl s (_ bv13 53)) t) (= (bvshl s (_ bv14 53)) t) (= (bvshl s (_ bv15 53)) t) (= (bvshl s (_ bv16 53)) t) (= (bvshl s (_ bv17 53)) t) (= (bvshl s (_ bv18 53)) t) (= (bvshl s (_ bv19 53)) t) (= (bvshl s (_ bv20 53)) t) (= (bvshl s (_ bv21 53)) t) (= (bvshl s (_ bv22 53)) t) (= (bvshl s (_ bv23 53)) t) (= (bvshl s (_ bv24 53)) t) (= (bvshl s (_ bv25 53)) t) (= (bvshl s (_ bv26 53)) t) (= (bvshl s (_ bv27 53)) t) (= (bvshl s (_ bv28 53)) t) (= (bvshl s (_ bv29 53)) t) (= (bvshl s (_ bv30 53)) t) (= (bvshl s (_ bv31 53)) t) (= (bvshl s (_ bv32 53)) t) (= (bvshl s (_ bv33 53)) t) (= (bvshl s (_ bv34 53)) t) (= (bvshl s (_ bv35 53)) t) (= (bvshl s (_ bv36 53)) t) (= (bvshl s (_ bv37 53)) t) (= (bvshl s (_ bv38 53)) t) (= (bvshl s (_ bv39 53)) t) (= (bvshl s (_ bv40 53)) t) (= (bvshl s (_ bv41 53)) t) (= (bvshl s (_ bv42 53)) t) (= (bvshl s (_ bv43 53)) t) (= (bvshl s (_ bv44 53)) t) (= (bvshl s (_ bv45 53)) t) (= (bvshl s (_ bv46 53)) t) (= (bvshl s (_ bv47 53)) t) (= (bvshl s (_ bv48 53)) t) (= (bvshl s (_ bv49 53)) t) (= (bvshl s (_ bv50 53)) t) (= (bvshl s (_ bv51 53)) t) (= (bvshl s (_ bv52 53)) t) (= (bvshl s (_ bv53 53)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 53))) (= (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 53))) (= (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
