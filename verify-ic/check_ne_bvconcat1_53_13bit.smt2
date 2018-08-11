(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 13))
(declare-fun tx () (_ BitVec 53))
(declare-fun ts () (_ BitVec 13))

(define-fun min () (_ BitVec 53)
  (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53)))
)
(define-fun max () (_ BitVec 53)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 53))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 53))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
