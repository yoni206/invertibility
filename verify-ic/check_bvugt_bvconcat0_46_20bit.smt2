(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 20))
(declare-fun tx () (_ BitVec 46))
(declare-fun ts () (_ BitVec 20))

(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 46))) (bvugt s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 46))) (bvugt (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 46))) (bvugt (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
