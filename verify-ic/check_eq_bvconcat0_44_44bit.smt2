(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 44))
(declare-fun tx () (_ BitVec 44))
(declare-fun ts () (_ BitVec 44))

(define-fun min () (_ BitVec 44)
  (bvnot (bvlshr (bvnot (_ bv0 44)) (_ bv1 44)))
)
(define-fun max () (_ BitVec 44)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 44))) (= (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 44))) (= (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
