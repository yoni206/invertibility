(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun tx () (_ BitVec 29))
(declare-fun ts () (_ BitVec 37))

(define-fun min () (_ BitVec 29)
  (bvnot (bvlshr (bvnot (_ bv0 29)) (_ bv1 29)))
)
(define-fun max () (_ BitVec 29)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 29))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 29))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
