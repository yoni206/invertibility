(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 25))
(declare-fun tx () (_ BitVec 41))
(declare-fun ts () (_ BitVec 25))

(define-fun min () (_ BitVec 41)
  (bvnot (bvlshr (bvnot (_ bv0 41)) (_ bv1 41)))
)
(define-fun max () (_ BitVec 41)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 41))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 41))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
