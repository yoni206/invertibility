(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 27))
(declare-fun tx () (_ BitVec 27))
(declare-fun ts () (_ BitVec 27))

(define-fun min () (_ BitVec 27)
  (bvnot (bvlshr (bvnot (_ bv0 27)) (_ bv1 27)))
)
(define-fun max () (_ BitVec 27)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 27))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 27))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
