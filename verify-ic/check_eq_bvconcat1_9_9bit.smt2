(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 9))
(declare-fun tx () (_ BitVec 9))
(declare-fun ts () (_ BitVec 9))

(define-fun min () (_ BitVec 9)
  (bvnot (bvlshr (bvnot (_ bv0 9)) (_ bv1 9)))
)
(define-fun max () (_ BitVec 9)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 9))) (= (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 9))) (= (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
