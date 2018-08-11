(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 56))
(declare-fun tx () (_ BitVec 10))
(declare-fun ts () (_ BitVec 56))

(define-fun min () (_ BitVec 10)
  (bvnot (bvlshr (bvnot (_ bv0 10)) (_ bv1 10)))
)
(define-fun max () (_ BitVec 10)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 10))) (bvsgt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 10))) (bvsgt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
