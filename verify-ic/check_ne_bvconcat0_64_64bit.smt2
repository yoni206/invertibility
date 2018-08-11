(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 64))
(declare-fun tx () (_ BitVec 64))
(declare-fun ts () (_ BitVec 64))

(define-fun min () (_ BitVec 64)
  (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64)))
)
(define-fun max () (_ BitVec 64)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 64))) (distinct (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 64))) (distinct (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
