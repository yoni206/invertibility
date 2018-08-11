(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 26))
(declare-fun tx () (_ BitVec 40))
(declare-fun ts () (_ BitVec 26))

(define-fun min () (_ BitVec 40)
  (bvnot (bvlshr (bvnot (_ bv0 40)) (_ bv1 40)))
)
(define-fun max () (_ BitVec 40)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 40)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 40))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 40))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
