(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 49))
(declare-fun tx () (_ BitVec 17))
(declare-fun ts () (_ BitVec 49))

(define-fun min () (_ BitVec 17)
  (bvnot (bvlshr (bvnot (_ bv0 17)) (_ bv1 17)))
)
(define-fun max () (_ BitVec 17)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 17))) (bvsge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 17))) (bvsge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
