(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 44))
(declare-fun tx () (_ BitVec 22))
(declare-fun ts () (_ BitVec 44))

(define-fun min () (_ BitVec 22)
  (bvnot (bvlshr (bvnot (_ bv0 22)) (_ bv1 22)))
)
(define-fun max () (_ BitVec 22)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 22))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 22))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
