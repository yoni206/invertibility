(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 45))
(declare-fun t () (_ BitVec 45))

(define-fun udivtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) (bvnot (_ bv0 45)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 45)) (b (_ BitVec 45))) (_ BitVec 45)
  (ite (= b (_ bv0 45)) a (bvurem a b))
)
(define-fun min () (_ BitVec 45)
  (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45)))
)
(define-fun max () (_ BitVec 45)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 45)) (t (_ BitVec 45))) Bool
(or  (bvsgt (bvshl s (_ bv0 45)) t) (bvsgt (bvshl s (_ bv1 45)) t) (bvsgt (bvshl s (_ bv2 45)) t) (bvsgt (bvshl s (_ bv3 45)) t) (bvsgt (bvshl s (_ bv4 45)) t) (bvsgt (bvshl s (_ bv5 45)) t) (bvsgt (bvshl s (_ bv6 45)) t) (bvsgt (bvshl s (_ bv7 45)) t) (bvsgt (bvshl s (_ bv8 45)) t) (bvsgt (bvshl s (_ bv9 45)) t) (bvsgt (bvshl s (_ bv10 45)) t) (bvsgt (bvshl s (_ bv11 45)) t) (bvsgt (bvshl s (_ bv12 45)) t) (bvsgt (bvshl s (_ bv13 45)) t) (bvsgt (bvshl s (_ bv14 45)) t) (bvsgt (bvshl s (_ bv15 45)) t) (bvsgt (bvshl s (_ bv16 45)) t) (bvsgt (bvshl s (_ bv17 45)) t) (bvsgt (bvshl s (_ bv18 45)) t) (bvsgt (bvshl s (_ bv19 45)) t) (bvsgt (bvshl s (_ bv20 45)) t) (bvsgt (bvshl s (_ bv21 45)) t) (bvsgt (bvshl s (_ bv22 45)) t) (bvsgt (bvshl s (_ bv23 45)) t) (bvsgt (bvshl s (_ bv24 45)) t) (bvsgt (bvshl s (_ bv25 45)) t) (bvsgt (bvshl s (_ bv26 45)) t) (bvsgt (bvshl s (_ bv27 45)) t) (bvsgt (bvshl s (_ bv28 45)) t) (bvsgt (bvshl s (_ bv29 45)) t) (bvsgt (bvshl s (_ bv30 45)) t) (bvsgt (bvshl s (_ bv31 45)) t) (bvsgt (bvshl s (_ bv32 45)) t) (bvsgt (bvshl s (_ bv33 45)) t) (bvsgt (bvshl s (_ bv34 45)) t) (bvsgt (bvshl s (_ bv35 45)) t) (bvsgt (bvshl s (_ bv36 45)) t) (bvsgt (bvshl s (_ bv37 45)) t) (bvsgt (bvshl s (_ bv38 45)) t) (bvsgt (bvshl s (_ bv39 45)) t) (bvsgt (bvshl s (_ bv40 45)) t) (bvsgt (bvshl s (_ bv41 45)) t) (bvsgt (bvshl s (_ bv42 45)) t) (bvsgt (bvshl s (_ bv43 45)) t) (bvsgt (bvshl s (_ bv44 45)) t) (bvsgt (bvshl s (_ bv45 45)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 45))) (bvsgt (bvshl s x) t)))
  (=> (exists ((x (_ BitVec 45))) (bvsgt (bvshl s x) t)) (SC s t))
  )
 )
)
(check-sat)
