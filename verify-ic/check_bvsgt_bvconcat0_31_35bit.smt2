(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 35))
(declare-fun tx () (_ BitVec 31))
(declare-fun ts () (_ BitVec 35))

(define-fun min () (_ BitVec 31)
  (bvnot (bvlshr (bvnot (_ bv0 31)) (_ bv1 31)))
)
(define-fun max () (_ BitVec 31)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 31))) (bvsgt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 31))) (bvsgt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
