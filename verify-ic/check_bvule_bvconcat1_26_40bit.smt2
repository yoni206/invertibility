(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 40))
(declare-fun tx () (_ BitVec 26))
(declare-fun ts () (_ BitVec 40))

(define-fun min () (_ BitVec 26)
  (bvnot (bvlshr (bvnot (_ bv0 26)) (_ bv1 26)))
)
(define-fun max () (_ BitVec 26)
  (bvnot min)
)

(define-fun SC () Bool
(bvule s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 26))) (bvule (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 26))) (bvule (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
