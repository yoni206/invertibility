(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 63))
(declare-fun tx () (_ BitVec 3))
(declare-fun ts () (_ BitVec 63))

(define-fun min () (_ BitVec 3)
  (bvnot (bvlshr (bvnot (_ bv0 3)) (_ bv1 3)))
)
(define-fun max () (_ BitVec 3)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 3))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 3))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 3))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
