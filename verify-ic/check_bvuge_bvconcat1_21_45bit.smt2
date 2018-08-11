(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 45))
(declare-fun tx () (_ BitVec 21))
(declare-fun ts () (_ BitVec 45))

(define-fun min () (_ BitVec 21)
  (bvnot (bvlshr (bvnot (_ bv0 21)) (_ bv1 21)))
)
(define-fun max () (_ BitVec 21)
  (bvnot min)
)

(define-fun SC () Bool
(bvuge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 21))) (bvuge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 21))) (bvuge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
