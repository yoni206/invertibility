(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun tx () (_ BitVec 59))
(declare-fun ts () (_ BitVec 7))

(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 59))) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 59))) (bvugt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 59))) (bvugt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
