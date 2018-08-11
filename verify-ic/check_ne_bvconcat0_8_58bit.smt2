(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 58))
(declare-fun tx () (_ BitVec 8))
(declare-fun ts () (_ BitVec 58))

(define-fun min () (_ BitVec 8)
  (bvnot (bvlshr (bvnot (_ bv0 8)) (_ bv1 8)))
)
(define-fun max () (_ BitVec 8)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 8))) (distinct (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 8))) (distinct (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
