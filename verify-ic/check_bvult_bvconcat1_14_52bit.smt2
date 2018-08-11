(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 52))
(declare-fun tx () (_ BitVec 14))
(declare-fun ts () (_ BitVec 52))

(define-fun min () (_ BitVec 14)
  (bvnot (bvlshr (bvnot (_ bv0 14)) (_ bv1 14)))
)
(define-fun max () (_ BitVec 14)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 14))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 14))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 14))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
