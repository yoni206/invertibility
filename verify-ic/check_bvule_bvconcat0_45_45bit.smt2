(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 45))
(declare-fun tx () (_ BitVec 45))
(declare-fun ts () (_ BitVec 45))

(define-fun min () (_ BitVec 45)
  (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45)))
)
(define-fun max () (_ BitVec 45)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (_ bv0 45)) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 45))) (bvule (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 45))) (bvule (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
