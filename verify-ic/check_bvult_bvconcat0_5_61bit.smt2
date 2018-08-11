(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 61))
(declare-fun tx () (_ BitVec 5))
(declare-fun ts () (_ BitVec 61))

(define-fun min () (_ BitVec 5)
  (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5)))
)
(define-fun max () (_ BitVec 5)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 5)) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 5))) (bvult (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 5))) (bvult (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
