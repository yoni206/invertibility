(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 6))
(declare-fun tx () (_ BitVec 60))
(declare-fun ts () (_ BitVec 6))

(define-fun min () (_ BitVec 60)
  (bvnot (bvlshr (bvnot (_ bv0 60)) (_ bv1 60)))
)
(define-fun max () (_ BitVec 60)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 60))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 60))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
