(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 12))
(declare-fun tx () (_ BitVec 12))
(declare-fun ts () (_ BitVec 12))

(define-fun min () (_ BitVec 12)
  (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12)))
)
(define-fun max () (_ BitVec 12)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 12))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 12))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 12))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
