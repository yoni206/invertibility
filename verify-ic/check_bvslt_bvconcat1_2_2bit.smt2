(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 2))
(declare-fun tx () (_ BitVec 2))
(declare-fun ts () (_ BitVec 2))

(define-fun min () (_ BitVec 2)
  (bvnot (bvlshr (bvnot (_ bv0 2)) (_ bv1 2)))
)
(define-fun max () (_ BitVec 2)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 2))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 2))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 2))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
