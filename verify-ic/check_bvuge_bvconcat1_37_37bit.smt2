(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 37))
(declare-fun tx () (_ BitVec 37))
(declare-fun ts () (_ BitVec 37))

(define-fun min () (_ BitVec 37)
  (bvnot (bvlshr (bvnot (_ bv0 37)) (_ bv1 37)))
)
(define-fun max () (_ BitVec 37)
  (bvnot min)
)

(define-fun SC () Bool
(bvuge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 37))) (bvuge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 37))) (bvuge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
