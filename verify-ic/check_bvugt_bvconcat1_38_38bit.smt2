(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 38))
(declare-fun tx () (_ BitVec 38))
(declare-fun ts () (_ BitVec 38))

(define-fun min () (_ BitVec 38)
  (bvnot (bvlshr (bvnot (_ bv0 38)) (_ bv1 38)))
)
(define-fun max () (_ BitVec 38)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 38)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 38))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 38))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
