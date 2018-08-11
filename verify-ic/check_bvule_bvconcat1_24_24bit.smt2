(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 24))
(declare-fun tx () (_ BitVec 24))
(declare-fun ts () (_ BitVec 24))

(define-fun min () (_ BitVec 24)
  (bvnot (bvlshr (bvnot (_ bv0 24)) (_ bv1 24)))
)
(define-fun max () (_ BitVec 24)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 24))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 24))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
