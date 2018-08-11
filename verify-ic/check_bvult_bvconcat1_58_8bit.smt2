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
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 58))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 58))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 58))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
