(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 47))
(declare-fun t () (_ BitVec 47))

(define-fun udivtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) (bvnot (_ bv0 47)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 47)) (b (_ BitVec 47))) (_ BitVec 47)
  (ite (= b (_ bv0 47)) a (bvurem a b))
)
(define-fun min () (_ BitVec 47)
  (bvnot (bvlshr (bvnot (_ bv0 47)) (_ bv1 47)))
)
(define-fun max () (_ BitVec 47)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 47)) (t (_ BitVec 47))) Bool
(or  (bvugt (bvshl s (_ bv0 47)) t) (bvugt (bvshl s (_ bv1 47)) t) (bvugt (bvshl s (_ bv2 47)) t) (bvugt (bvshl s (_ bv3 47)) t) (bvugt (bvshl s (_ bv4 47)) t) (bvugt (bvshl s (_ bv5 47)) t) (bvugt (bvshl s (_ bv6 47)) t) (bvugt (bvshl s (_ bv7 47)) t) (bvugt (bvshl s (_ bv8 47)) t) (bvugt (bvshl s (_ bv9 47)) t) (bvugt (bvshl s (_ bv10 47)) t) (bvugt (bvshl s (_ bv11 47)) t) (bvugt (bvshl s (_ bv12 47)) t) (bvugt (bvshl s (_ bv13 47)) t) (bvugt (bvshl s (_ bv14 47)) t) (bvugt (bvshl s (_ bv15 47)) t) (bvugt (bvshl s (_ bv16 47)) t) (bvugt (bvshl s (_ bv17 47)) t) (bvugt (bvshl s (_ bv18 47)) t) (bvugt (bvshl s (_ bv19 47)) t) (bvugt (bvshl s (_ bv20 47)) t) (bvugt (bvshl s (_ bv21 47)) t) (bvugt (bvshl s (_ bv22 47)) t) (bvugt (bvshl s (_ bv23 47)) t) (bvugt (bvshl s (_ bv24 47)) t) (bvugt (bvshl s (_ bv25 47)) t) (bvugt (bvshl s (_ bv26 47)) t) (bvugt (bvshl s (_ bv27 47)) t) (bvugt (bvshl s (_ bv28 47)) t) (bvugt (bvshl s (_ bv29 47)) t) (bvugt (bvshl s (_ bv30 47)) t) (bvugt (bvshl s (_ bv31 47)) t) (bvugt (bvshl s (_ bv32 47)) t) (bvugt (bvshl s (_ bv33 47)) t) (bvugt (bvshl s (_ bv34 47)) t) (bvugt (bvshl s (_ bv35 47)) t) (bvugt (bvshl s (_ bv36 47)) t) (bvugt (bvshl s (_ bv37 47)) t) (bvugt (bvshl s (_ bv38 47)) t) (bvugt (bvshl s (_ bv39 47)) t) (bvugt (bvshl s (_ bv40 47)) t) (bvugt (bvshl s (_ bv41 47)) t) (bvugt (bvshl s (_ bv42 47)) t) (bvugt (bvshl s (_ bv43 47)) t) (bvugt (bvshl s (_ bv44 47)) t) (bvugt (bvshl s (_ bv45 47)) t) (bvugt (bvshl s (_ bv46 47)) t) (bvugt (bvshl s (_ bv47 47)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 47))) (bvugt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 47))) (bvugt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
