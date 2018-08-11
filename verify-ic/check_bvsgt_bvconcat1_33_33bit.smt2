(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 33))
(declare-fun tx () (_ BitVec 33))
(declare-fun ts () (_ BitVec 33))

(define-fun min () (_ BitVec 33)
  (bvnot (bvlshr (bvnot (_ bv0 33)) (_ bv1 33)))
)
(define-fun max () (_ BitVec 33)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 33)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 33))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 33))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
