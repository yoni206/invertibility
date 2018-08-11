(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 8))
(declare-fun tx () (_ BitVec 58))
(declare-fun ts () (_ BitVec 8))

(define-fun min () (_ BitVec 58)
  (bvnot (bvlshr (bvnot (_ bv0 58)) (_ bv1 58)))
)
(define-fun max () (_ BitVec 58)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 58))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 58))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 58))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
