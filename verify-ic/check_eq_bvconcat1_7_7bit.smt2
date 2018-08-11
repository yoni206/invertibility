(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 7))
(declare-fun tx () (_ BitVec 7))
(declare-fun ts () (_ BitVec 7))

(define-fun min () (_ BitVec 7)
  (bvnot (bvlshr (bvnot (_ bv0 7)) (_ bv1 7)))
)
(define-fun max () (_ BitVec 7)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 7))) (= (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 7))) (= (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
