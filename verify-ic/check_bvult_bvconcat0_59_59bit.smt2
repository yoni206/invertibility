(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 59))
(declare-fun tx () (_ BitVec 59))
(declare-fun ts () (_ BitVec 59))

(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 59)) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 59))) (bvult (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 59))) (bvult (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
