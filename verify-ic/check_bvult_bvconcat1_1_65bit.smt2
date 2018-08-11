(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 65))
(declare-fun tx () (_ BitVec 1))
(declare-fun ts () (_ BitVec 65))

(define-fun min () (_ BitVec 1)
  (bvnot (bvlshr (bvnot (_ bv0 1)) (_ bv1 1)))
)
(define-fun max () (_ BitVec 1)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 1))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 1))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 1))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
