(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 19))
(declare-fun tx () (_ BitVec 19))
(declare-fun ts () (_ BitVec 19))

(define-fun min () (_ BitVec 19)
  (bvnot (bvlshr (bvnot (_ bv0 19)) (_ bv1 19)))
)
(define-fun max () (_ BitVec 19)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 19))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 19))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 19))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
