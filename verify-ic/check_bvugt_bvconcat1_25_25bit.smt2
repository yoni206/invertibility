(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 25))
(declare-fun tx () (_ BitVec 25))
(declare-fun ts () (_ BitVec 25))

(define-fun min () (_ BitVec 25)
  (bvnot (bvlshr (bvnot (_ bv0 25)) (_ bv1 25)))
)
(define-fun max () (_ BitVec 25)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 25)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 25))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 25))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
