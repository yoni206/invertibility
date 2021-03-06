(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun tx () (_ BitVec 7))
(declare-fun ts () (_ BitVec 7))

(define-fun min () (_ BitVec 7)
  (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7)))
)
(define-fun max () (_ BitVec 7)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvult s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 7))) (bvslt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 7))) (bvslt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
