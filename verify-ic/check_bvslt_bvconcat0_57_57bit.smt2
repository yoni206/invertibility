(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun tx () (_ BitVec 57))
(declare-fun ts () (_ BitVec 57))

(define-fun min () (_ BitVec 57)
  (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57)))
)
(define-fun max () (_ BitVec 57)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 57))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 57))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
