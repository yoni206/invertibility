(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 8))
(declare-fun tx () (_ BitVec 8))
(declare-fun ts () (_ BitVec 8))

(define-fun min () (_ BitVec 8)
  (bvnot (bvlshr (bvnot (_ bv0 8)) (_ bv1 8)))
)
(define-fun max () (_ BitVec 8)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 8)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 8))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 8))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
