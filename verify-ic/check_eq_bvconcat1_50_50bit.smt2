(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 50))
(declare-fun tx () (_ BitVec 50))
(declare-fun ts () (_ BitVec 50))

(define-fun min () (_ BitVec 50)
  (bvnot (bvlshr (bvnot (_ bv0 50)) (_ bv1 50)))
)
(define-fun max () (_ BitVec 50)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 50))) (= (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 50))) (= (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
