(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 23))
(declare-fun tx () (_ BitVec 23))
(declare-fun ts () (_ BitVec 23))

(define-fun min () (_ BitVec 23)
  (bvnot (bvlshr (bvnot (_ bv0 23)) (_ bv1 23)))
)
(define-fun max () (_ BitVec 23)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 23))) (bvsge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 23))) (bvsge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
