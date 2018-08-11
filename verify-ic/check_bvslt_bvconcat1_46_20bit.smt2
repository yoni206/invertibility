(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 20))
(declare-fun tx () (_ BitVec 46))
(declare-fun ts () (_ BitVec 20))

(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 46))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 46))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 46))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
