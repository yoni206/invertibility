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
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 62))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 62))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 62))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
