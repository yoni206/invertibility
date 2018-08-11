(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 46))
(declare-fun tx () (_ BitVec 20))
(declare-fun ts () (_ BitVec 46))

(define-fun min () (_ BitVec 20)
  (bvnot (bvlshr (bvnot (_ bv0 20)) (_ bv1 20)))
)
(define-fun max () (_ BitVec 20)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 20))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 20))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
