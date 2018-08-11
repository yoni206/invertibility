(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 53))
(declare-fun tx () (_ BitVec 53))
(declare-fun ts () (_ BitVec 53))

(define-fun min () (_ BitVec 53)
  (bvnot (bvlshr (bvnot (_ bv0 53)) (_ bv1 53)))
)
(define-fun max () (_ BitVec 53)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 53)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 53))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 53))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
