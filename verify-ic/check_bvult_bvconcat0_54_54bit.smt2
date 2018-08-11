(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 54))
(declare-fun tx () (_ BitVec 54))
(declare-fun ts () (_ BitVec 54))

(define-fun min () (_ BitVec 54)
  (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54)))
)
(define-fun max () (_ BitVec 54)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 54)) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 54))) (bvult (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 54))) (bvult (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
