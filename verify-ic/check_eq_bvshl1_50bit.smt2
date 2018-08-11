(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 50))
(declare-fun t () (_ BitVec 50))

(define-fun udivtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) (bvnot (_ bv0 50)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 50)) (b (_ BitVec 50))) (_ BitVec 50)
  (ite (= b (_ bv0 50)) a (bvurem a b))
)
(define-fun min () (_ BitVec 50)
  (bvnot (bvlshr (bvnot (_ bv0 50)) (_ bv1 50)))
)
(define-fun max () (_ BitVec 50)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 50)) (t (_ BitVec 50))) Bool
(or  (= (bvshl s (_ bv0 50)) t) (= (bvshl s (_ bv1 50)) t) (= (bvshl s (_ bv2 50)) t) (= (bvshl s (_ bv3 50)) t) (= (bvshl s (_ bv4 50)) t) (= (bvshl s (_ bv5 50)) t) (= (bvshl s (_ bv6 50)) t) (= (bvshl s (_ bv7 50)) t) (= (bvshl s (_ bv8 50)) t) (= (bvshl s (_ bv9 50)) t) (= (bvshl s (_ bv10 50)) t) (= (bvshl s (_ bv11 50)) t) (= (bvshl s (_ bv12 50)) t) (= (bvshl s (_ bv13 50)) t) (= (bvshl s (_ bv14 50)) t) (= (bvshl s (_ bv15 50)) t) (= (bvshl s (_ bv16 50)) t) (= (bvshl s (_ bv17 50)) t) (= (bvshl s (_ bv18 50)) t) (= (bvshl s (_ bv19 50)) t) (= (bvshl s (_ bv20 50)) t) (= (bvshl s (_ bv21 50)) t) (= (bvshl s (_ bv22 50)) t) (= (bvshl s (_ bv23 50)) t) (= (bvshl s (_ bv24 50)) t) (= (bvshl s (_ bv25 50)) t) (= (bvshl s (_ bv26 50)) t) (= (bvshl s (_ bv27 50)) t) (= (bvshl s (_ bv28 50)) t) (= (bvshl s (_ bv29 50)) t) (= (bvshl s (_ bv30 50)) t) (= (bvshl s (_ bv31 50)) t) (= (bvshl s (_ bv32 50)) t) (= (bvshl s (_ bv33 50)) t) (= (bvshl s (_ bv34 50)) t) (= (bvshl s (_ bv35 50)) t) (= (bvshl s (_ bv36 50)) t) (= (bvshl s (_ bv37 50)) t) (= (bvshl s (_ bv38 50)) t) (= (bvshl s (_ bv39 50)) t) (= (bvshl s (_ bv40 50)) t) (= (bvshl s (_ bv41 50)) t) (= (bvshl s (_ bv42 50)) t) (= (bvshl s (_ bv43 50)) t) (= (bvshl s (_ bv44 50)) t) (= (bvshl s (_ bv45 50)) t) (= (bvshl s (_ bv46 50)) t) (= (bvshl s (_ bv47 50)) t) (= (bvshl s (_ bv48 50)) t) (= (bvshl s (_ bv49 50)) t) (= (bvshl s (_ bv50 50)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 50))) (= (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 50))) (= (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
