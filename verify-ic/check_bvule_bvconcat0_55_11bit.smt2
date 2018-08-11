(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun tx () (_ BitVec 55))
(declare-fun ts () (_ BitVec 11))

(define-fun min () (_ BitVec 55)
  (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55)))
)
(define-fun max () (_ BitVec 55)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 55)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 55))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 55))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
