(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 44))
(declare-fun tx () (_ BitVec 22))
(declare-fun ts () (_ BitVec 44))

(define-fun min () (_ BitVec 22)
  (bvnot (bvlshr (bvnot (_ bv0 22)) (_ bv1 22)))
)
(define-fun max () (_ BitVec 22)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 22)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 22))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 22))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
