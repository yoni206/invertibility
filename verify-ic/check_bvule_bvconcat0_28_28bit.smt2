(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 28))
(declare-fun tx () (_ BitVec 28))
(declare-fun ts () (_ BitVec 28))

(define-fun min () (_ BitVec 28)
  (bvnot (bvlshr (bvnot (_ bv0 28)) (_ bv1 28)))
)
(define-fun max () (_ BitVec 28)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 28)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 28))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 28))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
