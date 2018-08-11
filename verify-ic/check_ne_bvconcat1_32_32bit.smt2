(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 32))
(declare-fun tx () (_ BitVec 32))
(declare-fun ts () (_ BitVec 32))

(define-fun min () (_ BitVec 32)
  (bvnot (bvlshr (bvnot (_ bv0 32)) (_ bv1 32)))
)
(define-fun max () (_ BitVec 32)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 32))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 32))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
