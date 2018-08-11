(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 3))
(declare-fun tx () (_ BitVec 3))
(declare-fun ts () (_ BitVec 3))

(define-fun min () (_ BitVec 3)
  (bvnot (bvlshr (bvnot (_ bv0 3)) (_ bv1 3)))
)
(define-fun max () (_ BitVec 3)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 3))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 3))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
