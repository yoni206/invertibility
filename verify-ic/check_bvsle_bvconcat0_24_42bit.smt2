(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 42))
(declare-fun tx () (_ BitVec 24))
(declare-fun ts () (_ BitVec 42))

(define-fun min () (_ BitVec 24)
  (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24)))
)
(define-fun max () (_ BitVec 24)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 24))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 24))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
