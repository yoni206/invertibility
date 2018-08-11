(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 10))
(declare-fun tx () (_ BitVec 56))
(declare-fun ts () (_ BitVec 10))

(define-fun min () (_ BitVec 56)
  (bvnot (bvlshr (bvnot (_ bv0 56)) (_ bv1 56)))
)
(define-fun max () (_ BitVec 56)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 56))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 56))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 56))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
