(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 6))
(declare-fun tx () (_ BitVec 60))
(declare-fun ts () (_ BitVec 6))

(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 60)) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 60))) (bvult (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 60))) (bvult (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
