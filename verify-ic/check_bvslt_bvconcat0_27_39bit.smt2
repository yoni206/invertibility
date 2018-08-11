(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 39))
(declare-fun tx () (_ BitVec 27))
(declare-fun ts () (_ BitVec 39))

(define-fun min () (_ BitVec 27)
  (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27)))
)
(define-fun max () (_ BitVec 27)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 27))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 27))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
