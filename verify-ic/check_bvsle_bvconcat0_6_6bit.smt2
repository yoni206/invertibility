(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 6))
(declare-fun tx () (_ BitVec 6))
(declare-fun ts () (_ BitVec 6))

(define-fun min () (_ BitVec 6)
  (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6)))
)
(define-fun max () (_ BitVec 6)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 6))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 6))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
