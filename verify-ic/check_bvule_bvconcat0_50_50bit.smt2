(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 50))
(declare-fun tx () (_ BitVec 50))
(declare-fun ts () (_ BitVec 50))

(define-fun min () (_ BitVec 50)
  (bvnot (bvlshr (bvnot (_ bv0 50)) (_ bv1 50)))
)
(define-fun max () (_ BitVec 50)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 50)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 50))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 50))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
