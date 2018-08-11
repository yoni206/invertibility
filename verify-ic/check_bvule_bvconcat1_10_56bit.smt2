(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 56))
(declare-fun tx () (_ BitVec 10))
(declare-fun ts () (_ BitVec 56))

(define-fun min () (_ BitVec 10)
  (bvnot (bvlshr (bvnot (_ bv0 10)) (_ bv1 10)))
)
(define-fun max () (_ BitVec 10)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 10))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 10))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
