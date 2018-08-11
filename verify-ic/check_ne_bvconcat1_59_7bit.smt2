(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun tx () (_ BitVec 59))
(declare-fun ts () (_ BitVec 7))

(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 59))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 59))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
