(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 49))
(declare-fun tx () (_ BitVec 49))
(declare-fun ts () (_ BitVec 49))

(define-fun min () (_ BitVec 49)
  (bvnot (bvlshr (bvnot (_ bv0 49)) (_ bv1 49)))
)
(define-fun max () (_ BitVec 49)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 49))) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 49))) (bvugt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 49))) (bvugt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
