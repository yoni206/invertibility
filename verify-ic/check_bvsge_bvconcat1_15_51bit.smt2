(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 51))
(declare-fun tx () (_ BitVec 15))
(declare-fun ts () (_ BitVec 51))

(define-fun min () (_ BitVec 15)
  (bvnot (bvlshr (bvnot (_ bv0 15)) (_ bv1 15)))
)
(define-fun max () (_ BitVec 15)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 15))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 15))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
