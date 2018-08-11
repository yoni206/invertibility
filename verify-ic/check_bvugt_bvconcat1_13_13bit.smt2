(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 13))
(declare-fun tx () (_ BitVec 13))
(declare-fun ts () (_ BitVec 13))

(define-fun min () (_ BitVec 13)
  (bvnot (bvlshr (bvnot (_ bv0 13)) (_ bv1 13)))
)
(define-fun max () (_ BitVec 13)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 13)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 13))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 13))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
