(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 18))
(declare-fun tx () (_ BitVec 48))
(declare-fun ts () (_ BitVec 18))

(define-fun min () (_ BitVec 48)
  (bvnot (bvlshr (bvnot (_ bv0 48)) (_ bv1 48)))
)
(define-fun max () (_ BitVec 48)
  (bvnot min)
)

(define-fun SC () Bool
(bvuge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 48))) (bvuge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 48))) (bvuge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
