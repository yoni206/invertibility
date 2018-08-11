(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 41))
(declare-fun tx () (_ BitVec 25))
(declare-fun ts () (_ BitVec 41))

(define-fun min () (_ BitVec 25)
  (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25)))
)
(define-fun max () (_ BitVec 25)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 25))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 25))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
