(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 15))
(declare-fun tx () (_ BitVec 51))
(declare-fun ts () (_ BitVec 15))

(define-fun min () (_ BitVec 51)
  (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51)))
)
(define-fun max () (_ BitVec 51)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 51))) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 51))) (bvugt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 51))) (bvugt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
