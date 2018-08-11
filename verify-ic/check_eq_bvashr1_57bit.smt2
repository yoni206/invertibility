(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun t () (_ BitVec 57))

(define-fun udivtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) (bvnot (_ bv0 57)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 57)) (b (_ BitVec 57))) (_ BitVec 57)
  (ite (= b (_ bv0 57)) a (bvurem a b))
)
(define-fun min () (_ BitVec 57)
  (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57)))
)
(define-fun max () (_ BitVec 57)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 57)) (t (_ BitVec 57))) Bool
(or  (= (bvashr s (_ bv0 57)) t) (= (bvashr s (_ bv1 57)) t) (= (bvashr s (_ bv2 57)) t) (= (bvashr s (_ bv3 57)) t) (= (bvashr s (_ bv4 57)) t) (= (bvashr s (_ bv5 57)) t) (= (bvashr s (_ bv6 57)) t) (= (bvashr s (_ bv7 57)) t) (= (bvashr s (_ bv8 57)) t) (= (bvashr s (_ bv9 57)) t) (= (bvashr s (_ bv10 57)) t) (= (bvashr s (_ bv11 57)) t) (= (bvashr s (_ bv12 57)) t) (= (bvashr s (_ bv13 57)) t) (= (bvashr s (_ bv14 57)) t) (= (bvashr s (_ bv15 57)) t) (= (bvashr s (_ bv16 57)) t) (= (bvashr s (_ bv17 57)) t) (= (bvashr s (_ bv18 57)) t) (= (bvashr s (_ bv19 57)) t) (= (bvashr s (_ bv20 57)) t) (= (bvashr s (_ bv21 57)) t) (= (bvashr s (_ bv22 57)) t) (= (bvashr s (_ bv23 57)) t) (= (bvashr s (_ bv24 57)) t) (= (bvashr s (_ bv25 57)) t) (= (bvashr s (_ bv26 57)) t) (= (bvashr s (_ bv27 57)) t) (= (bvashr s (_ bv28 57)) t) (= (bvashr s (_ bv29 57)) t) (= (bvashr s (_ bv30 57)) t) (= (bvashr s (_ bv31 57)) t) (= (bvashr s (_ bv32 57)) t) (= (bvashr s (_ bv33 57)) t) (= (bvashr s (_ bv34 57)) t) (= (bvashr s (_ bv35 57)) t) (= (bvashr s (_ bv36 57)) t) (= (bvashr s (_ bv37 57)) t) (= (bvashr s (_ bv38 57)) t) (= (bvashr s (_ bv39 57)) t) (= (bvashr s (_ bv40 57)) t) (= (bvashr s (_ bv41 57)) t) (= (bvashr s (_ bv42 57)) t) (= (bvashr s (_ bv43 57)) t) (= (bvashr s (_ bv44 57)) t) (= (bvashr s (_ bv45 57)) t) (= (bvashr s (_ bv46 57)) t) (= (bvashr s (_ bv47 57)) t) (= (bvashr s (_ bv48 57)) t) (= (bvashr s (_ bv49 57)) t) (= (bvashr s (_ bv50 57)) t) (= (bvashr s (_ bv51 57)) t) (= (bvashr s (_ bv52 57)) t) (= (bvashr s (_ bv53 57)) t) (= (bvashr s (_ bv54 57)) t) (= (bvashr s (_ bv55 57)) t) (= (bvashr s (_ bv56 57)) t) (= (bvashr s (_ bv57 57)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 57))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 57))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
