(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 1))
(declare-fun tx () (_ BitVec 65))
(declare-fun ts () (_ BitVec 1))

(define-fun min () (_ BitVec 65)
  (bvnot (bvlshr (bvnot (_ bv0 65)) (_ bv1 65)))
)
(define-fun max () (_ BitVec 65)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 65))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 65))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
