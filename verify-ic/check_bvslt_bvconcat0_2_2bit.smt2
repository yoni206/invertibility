(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 2))
(declare-fun tx () (_ BitVec 2))
(declare-fun ts () (_ BitVec 2))

(define-fun min () (_ BitVec 2)
  (bvnot (bvlshr (bvnot (_ bv0 2)) (_ bv1 2)))
)
(define-fun max () (_ BitVec 2)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 2))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 2))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
