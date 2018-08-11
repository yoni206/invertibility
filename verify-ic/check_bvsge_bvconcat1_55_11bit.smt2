(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun tx () (_ BitVec 55))
(declare-fun ts () (_ BitVec 11))

(define-fun min () (_ BitVec 55)
  (bvnot (bvlshr (bvnot (_ bv0 55)) (_ bv1 55)))
)
(define-fun max () (_ BitVec 55)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 55))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 55))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
