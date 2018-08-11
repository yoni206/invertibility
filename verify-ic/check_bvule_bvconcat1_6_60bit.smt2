(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 60))
(declare-fun tx () (_ BitVec 6))
(declare-fun ts () (_ BitVec 60))

(define-fun min () (_ BitVec 6)
  (bvnot (bvlshr (bvnot (_ bv0 6)) (_ bv1 6)))
)
(define-fun max () (_ BitVec 6)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 6))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 6))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
