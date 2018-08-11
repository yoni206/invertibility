(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 30))
(declare-fun tx () (_ BitVec 30))
(declare-fun ts () (_ BitVec 30))

(define-fun min () (_ BitVec 30)
  (bvnot (bvlshr (bvnot (_ bv0 30)) (_ bv1 30)))
)
(define-fun max () (_ BitVec 30)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 30))) (= (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 30))) (= (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
