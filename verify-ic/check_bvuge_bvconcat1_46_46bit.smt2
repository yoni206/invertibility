(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 46))
(declare-fun tx () (_ BitVec 46))
(declare-fun ts () (_ BitVec 46))

(define-fun min () (_ BitVec 46)
  (bvnot (bvlshr (bvnot (_ bv0 46)) (_ bv1 46)))
)
(define-fun max () (_ BitVec 46)
  (bvnot min)
)

(define-fun SC () Bool
(bvuge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 46))) (bvuge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 46))) (bvuge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
