(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 41))
(declare-fun tx () (_ BitVec 41))
(declare-fun ts () (_ BitVec 41))

(define-fun min () (_ BitVec 41)
  (bvnot (bvlshr (bvnot (_ bv0 41)) (_ bv1 41)))
)
(define-fun max () (_ BitVec 41)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 41))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 41))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 41))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
