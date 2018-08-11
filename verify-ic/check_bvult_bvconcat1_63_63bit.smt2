(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun tx () (_ BitVec 63))
(declare-fun ts () (_ BitVec 63))

(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 63))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 63))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 63))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
