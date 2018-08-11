(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 52))
(declare-fun tx () (_ BitVec 52))
(declare-fun ts () (_ BitVec 52))

(define-fun min () (_ BitVec 52)
  (bvnot (bvlshr (bvnot (_ bv0 52)) (_ bv1 52)))
)
(define-fun max () (_ BitVec 52)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 52))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 52))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
