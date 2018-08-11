(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 38))
(declare-fun tx () (_ BitVec 28))
(declare-fun ts () (_ BitVec 38))

(define-fun min () (_ BitVec 28)
  (bvnot (bvlshr (bvnot (_ bv0 28)) (_ bv1 28)))
)
(define-fun max () (_ BitVec 28)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 28))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 28))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
