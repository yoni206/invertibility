(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 50))
(declare-fun tx () (_ BitVec 16))
(declare-fun ts () (_ BitVec 50))

(define-fun min () (_ BitVec 16)
  (bvnot (bvlshr (bvnot (_ bv0 16)) (_ bv1 16)))
)
(define-fun max () (_ BitVec 16)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 16)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 16))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 16))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
