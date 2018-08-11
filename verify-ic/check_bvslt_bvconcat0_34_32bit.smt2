(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun tx () (_ BitVec 34))
(declare-fun ts () (_ BitVec 32))

(define-fun min () (_ BitVec 34)
  (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34)))
)
(define-fun max () (_ BitVec 34)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 34))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 34))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
