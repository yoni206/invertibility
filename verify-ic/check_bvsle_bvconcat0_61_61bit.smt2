(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 61))
(declare-fun tx () (_ BitVec 61))
(declare-fun ts () (_ BitVec 61))

(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 61))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 61))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
