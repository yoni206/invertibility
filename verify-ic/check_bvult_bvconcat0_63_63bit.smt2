(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun tx () (_ BitVec 63))
(declare-fun ts () (_ BitVec 63))

(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 63)) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 63))) (bvult (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 63))) (bvult (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
