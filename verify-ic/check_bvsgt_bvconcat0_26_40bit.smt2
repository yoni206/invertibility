(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 40))
(declare-fun tx () (_ BitVec 26))
(declare-fun ts () (_ BitVec 40))

(define-fun min () (_ BitVec 26)
  (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26)))
)
(define-fun max () (_ BitVec 26)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 26))) (bvsgt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 26))) (bvsgt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
