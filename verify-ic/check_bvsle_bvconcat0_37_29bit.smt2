(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 29))
(declare-fun tx () (_ BitVec 37))
(declare-fun ts () (_ BitVec 29))

(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 37))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 37))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
