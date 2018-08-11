(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 61))
(declare-fun tx () (_ BitVec 61))
(declare-fun ts () (_ BitVec 61))

(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 61))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 61))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 61))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
