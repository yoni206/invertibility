(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 11))
(declare-fun tx () (_ BitVec 11))
(declare-fun ts () (_ BitVec 11))

(define-fun min () (_ BitVec 11)
  (bvnot (bvlshr (bvnot (_ bv0 11)) (_ bv1 11)))
)
(define-fun max () (_ BitVec 11)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 11))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 11))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 11))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
