(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun tx () (_ BitVec 34))
(declare-fun ts () (_ BitVec 32))

(define-fun min () (_ BitVec 34)
  (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34)))
)
(define-fun max () (_ BitVec 34)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 34))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 34))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
