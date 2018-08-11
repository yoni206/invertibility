(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 4))
(declare-fun tx () (_ BitVec 62))
(declare-fun ts () (_ BitVec 4))

(define-fun min () (_ BitVec 62)
  (bvnot (bvlshr (bvnot (_ bv0 62)) (_ bv1 62)))
)
(define-fun max () (_ BitVec 62)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 62))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 62))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
