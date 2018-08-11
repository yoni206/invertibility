(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 54))
(declare-fun tx () (_ BitVec 54))
(declare-fun ts () (_ BitVec 54))

(define-fun min () (_ BitVec 54)
  (bvnot (bvlshr (bvnot (_ bv0 54)) (_ bv1 54)))
)
(define-fun max () (_ BitVec 54)
  (bvnot min)
)

(define-fun SC () Bool
(bvsge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 54))) (bvsge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 54))) (bvsge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
