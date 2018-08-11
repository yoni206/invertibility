(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 62))
(declare-fun tx () (_ BitVec 62))
(declare-fun ts () (_ BitVec 62))

(define-fun min () (_ BitVec 62)
  (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62)))
)
(define-fun max () (_ BitVec 62)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx max) (bvuge s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 62))) (bvsge (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 62))) (bvsge (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
