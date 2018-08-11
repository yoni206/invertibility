(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 45))
(declare-fun tx () (_ BitVec 45))
(declare-fun ts () (_ BitVec 45))

(define-fun min () (_ BitVec 45)
  (bvnot (bvlshr (bvnot (_ bv0 45)) (_ bv1 45)))
)
(define-fun max () (_ BitVec 45)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 45))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 45))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 45))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
