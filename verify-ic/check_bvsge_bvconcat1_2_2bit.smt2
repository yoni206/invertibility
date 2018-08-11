(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 2))
(declare-fun tx () (_ BitVec 2))
(declare-fun ts () (_ BitVec 2))

(define-fun min () (_ BitVec 2)
  (bvnot (bvlshr (bvnot (_ bv0 2)) (_ bv1 2)))
)
(define-fun max () (_ BitVec 2)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 2))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 2))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
