(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 33))
(declare-fun tx () (_ BitVec 33))
(declare-fun ts () (_ BitVec 33))

(define-fun min () (_ BitVec 33)
  (bvnot (bvlshr (bvnot (_ bv0 33)) (_ bv1 33)))
)
(define-fun max () (_ BitVec 33)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 33))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 33))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 33))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
