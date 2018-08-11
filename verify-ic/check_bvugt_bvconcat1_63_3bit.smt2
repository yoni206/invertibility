(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 3))
(declare-fun tx () (_ BitVec 63))
(declare-fun ts () (_ BitVec 3))

(define-fun min () (_ BitVec 63)
  (bvnot (bvlshr (bvnot (_ bv0 63)) (_ bv1 63)))
)
(define-fun max () (_ BitVec 63)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 63)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 63))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 63))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
