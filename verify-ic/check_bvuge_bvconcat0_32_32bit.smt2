(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun tx () (_ BitVec 32))
(declare-fun ts () (_ BitVec 32))

(define-fun min () (_ BitVec 32)
  (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32)))
)
(define-fun max () (_ BitVec 32)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 32))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 32))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 32))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
