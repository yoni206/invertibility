(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun tx () (_ BitVec 11))
(declare-fun ts () (_ BitVec 11))

(define-fun min () (_ BitVec 11)
  (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11)))
)
(define-fun max () (_ BitVec 11)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 11))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 11))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
