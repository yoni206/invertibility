(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 26))
(declare-fun tx () (_ BitVec 26))
(declare-fun ts () (_ BitVec 26))

(define-fun min () (_ BitVec 26)
  (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26)))
)
(define-fun max () (_ BitVec 26)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvule s ts) (=> (= s ts) (distinct tx (_ bv0 26))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 26))) (bvult (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 26))) (bvult (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
