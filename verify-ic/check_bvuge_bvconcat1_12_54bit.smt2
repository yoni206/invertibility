(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 54))
(declare-fun tx () (_ BitVec 12))
(declare-fun ts () (_ BitVec 54))

(define-fun min () (_ BitVec 12)
  (bvnot (bvlshr (bvnot (_ bv0 12)) (_ bv1 12)))
)
(define-fun max () (_ BitVec 12)
  (bvnot min)
)

(define-fun SC () Bool
(bvuge s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 12))) (bvuge (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 12))) (bvuge (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
