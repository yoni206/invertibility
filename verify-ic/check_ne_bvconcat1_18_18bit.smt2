(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 18))
(declare-fun tx () (_ BitVec 18))
(declare-fun ts () (_ BitVec 18))

(define-fun min () (_ BitVec 18)
  (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18)))
)
(define-fun max () (_ BitVec 18)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 18))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 18))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
