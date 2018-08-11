(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun tx () (_ BitVec 57))
(declare-fun ts () (_ BitVec 57))

(define-fun min () (_ BitVec 57)
  (bvnot (bvlshr (bvnot (_ bv0 57)) (_ bv1 57)))
)
(define-fun max () (_ BitVec 57)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 57))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 57))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
