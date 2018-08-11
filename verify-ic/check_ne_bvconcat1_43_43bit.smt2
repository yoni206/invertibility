(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 43))
(declare-fun tx () (_ BitVec 43))
(declare-fun ts () (_ BitVec 43))

(define-fun min () (_ BitVec 43)
  (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43)))
)
(define-fun max () (_ BitVec 43)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 43))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 43))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
