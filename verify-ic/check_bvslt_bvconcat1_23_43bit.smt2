(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 43))
(declare-fun tx () (_ BitVec 23))
(declare-fun ts () (_ BitVec 43))

(define-fun min () (_ BitVec 23)
  (bvnot (bvlshr (bvnot (_ bv0 23)) (_ bv1 23)))
)
(define-fun max () (_ BitVec 23)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 23))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 23))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 23))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
