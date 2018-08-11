(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 53))
(declare-fun tx () (_ BitVec 13))
(declare-fun ts () (_ BitVec 53))

(define-fun min () (_ BitVec 13)
  (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13)))
)
(define-fun max () (_ BitVec 13)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 13))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 13))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 13))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
