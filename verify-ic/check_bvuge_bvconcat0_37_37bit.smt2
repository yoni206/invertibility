(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun tx () (_ BitVec 37))
(declare-fun ts () (_ BitVec 37))

(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx (bvnot (_ bv0 37))) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 37))) (bvuge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 37))) (bvuge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
