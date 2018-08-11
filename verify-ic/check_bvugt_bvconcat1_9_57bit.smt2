(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 57))
(declare-fun tx () (_ BitVec 9))
(declare-fun ts () (_ BitVec 57))

(define-fun min () (_ BitVec 9)
  (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9)))
)
(define-fun max () (_ BitVec 9)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 9)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 9))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 9))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
