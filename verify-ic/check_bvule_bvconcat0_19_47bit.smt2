(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 47))
(declare-fun tx () (_ BitVec 19))
(declare-fun ts () (_ BitVec 47))

(define-fun min () (_ BitVec 19)
  (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19)))
)
(define-fun max () (_ BitVec 19)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 19)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 19))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 19))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
