(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun tx () (_ BitVec 39))
(declare-fun ts () (_ BitVec 27))

(define-fun min () (_ BitVec 39)
  (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39)))
)
(define-fun max () (_ BitVec 39)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 39))) (bvsge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 39))) (bvsge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
