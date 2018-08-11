(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun tx () (_ BitVec 9))
(declare-fun ts () (_ BitVec 57))

(define-fun min () (_ BitVec 9)
  (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9)))
)
(define-fun max () (_ BitVec 9)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 9))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 9))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 9))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
