(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 5))
(declare-fun tx () (_ BitVec 61))
(declare-fun ts () (_ BitVec 5))

(define-fun min () (_ BitVec 61)
  (bvnot (bvlshr (bvnot (_ bv0 61)) (_ bv1 61)))
)
(define-fun max () (_ BitVec 61)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 61)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 61))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 61))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
