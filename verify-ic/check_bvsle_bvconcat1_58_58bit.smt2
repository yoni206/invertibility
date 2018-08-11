(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 58))
(declare-fun tx () (_ BitVec 58))
(declare-fun ts () (_ BitVec 58))

(define-fun min () (_ BitVec 58)
  (bvnot (bvlshr (bvnot (_ bv0 58)) (_ bv1 58)))
)
(define-fun max () (_ BitVec 58)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 58))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 58))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
