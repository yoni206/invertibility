(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 48))
(declare-fun tx () (_ BitVec 18))
(declare-fun ts () (_ BitVec 48))

(define-fun min () (_ BitVec 18)
  (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18)))
)
(define-fun max () (_ BitVec 18)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 18))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 18))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
