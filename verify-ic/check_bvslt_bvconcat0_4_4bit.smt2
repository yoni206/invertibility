(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 4))
(declare-fun tx () (_ BitVec 4))
(declare-fun ts () (_ BitVec 4))

(define-fun min () (_ BitVec 4)
  (bvnot (bvlshr (bvnot (_ bv0 4)) (_ bv1 4)))
)
(define-fun max () (_ BitVec 4)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 4))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 4))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
