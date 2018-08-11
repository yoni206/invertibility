(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun tx () (_ BitVec 39))
(declare-fun ts () (_ BitVec 27))

(define-fun min () (_ BitVec 39)
  (bvnot (bvlshr (bvnot (_ bv0 39)) (_ bv1 39)))
)
(define-fun max () (_ BitVec 39)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 39))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 39))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
