(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 55))
(declare-fun t () (_ BitVec 55))

(define-fun udivtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) (bvnot (_ bv0 55)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec 55)) (b (_ BitVec 55))) (_ BitVec 55)
  (ite (= b (_ bv0 55)) a (bvurem a b))
)
(define-fun min () (_ BitVec 55)
  (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55)))
)
(define-fun max () (_ BitVec 55)
  (bvnot min)
)

(define-fun SC ((s (_ BitVec 55)) (t (_ BitVec 55))) Bool
(or  (= (bvashr s (_ bv0 55)) t) (= (bvashr s (_ bv1 55)) t) (= (bvashr s (_ bv2 55)) t) (= (bvashr s (_ bv3 55)) t) (= (bvashr s (_ bv4 55)) t) (= (bvashr s (_ bv5 55)) t) (= (bvashr s (_ bv6 55)) t) (= (bvashr s (_ bv7 55)) t) (= (bvashr s (_ bv8 55)) t) (= (bvashr s (_ bv9 55)) t) (= (bvashr s (_ bv10 55)) t) (= (bvashr s (_ bv11 55)) t) (= (bvashr s (_ bv12 55)) t) (= (bvashr s (_ bv13 55)) t) (= (bvashr s (_ bv14 55)) t) (= (bvashr s (_ bv15 55)) t) (= (bvashr s (_ bv16 55)) t) (= (bvashr s (_ bv17 55)) t) (= (bvashr s (_ bv18 55)) t) (= (bvashr s (_ bv19 55)) t) (= (bvashr s (_ bv20 55)) t) (= (bvashr s (_ bv21 55)) t) (= (bvashr s (_ bv22 55)) t) (= (bvashr s (_ bv23 55)) t) (= (bvashr s (_ bv24 55)) t) (= (bvashr s (_ bv25 55)) t) (= (bvashr s (_ bv26 55)) t) (= (bvashr s (_ bv27 55)) t) (= (bvashr s (_ bv28 55)) t) (= (bvashr s (_ bv29 55)) t) (= (bvashr s (_ bv30 55)) t) (= (bvashr s (_ bv31 55)) t) (= (bvashr s (_ bv32 55)) t) (= (bvashr s (_ bv33 55)) t) (= (bvashr s (_ bv34 55)) t) (= (bvashr s (_ bv35 55)) t) (= (bvashr s (_ bv36 55)) t) (= (bvashr s (_ bv37 55)) t) (= (bvashr s (_ bv38 55)) t) (= (bvashr s (_ bv39 55)) t) (= (bvashr s (_ bv40 55)) t) (= (bvashr s (_ bv41 55)) t) (= (bvashr s (_ bv42 55)) t) (= (bvashr s (_ bv43 55)) t) (= (bvashr s (_ bv44 55)) t) (= (bvashr s (_ bv45 55)) t) (= (bvashr s (_ bv46 55)) t) (= (bvashr s (_ bv47 55)) t) (= (bvashr s (_ bv48 55)) t) (= (bvashr s (_ bv49 55)) t) (= (bvashr s (_ bv50 55)) t) (= (bvashr s (_ bv51 55)) t) (= (bvashr s (_ bv52 55)) t) (= (bvashr s (_ bv53 55)) t) (= (bvashr s (_ bv54 55)) t) (= (bvashr s (_ bv55 55)) t))
)

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec 55))) (= (bvashr s x) t)))
  (=> (exists ((x (_ BitVec 55))) (= (bvashr s x) t)) (SC s t))
  )
 )
)
(check-sat)
