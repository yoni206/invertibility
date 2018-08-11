(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 36))
(declare-fun tx () (_ BitVec 30))
(declare-fun ts () (_ BitVec 36))

(define-fun min () (_ BitVec 30)
  (bvnot (bvlshr (bvnot (_ bv0 30)) (_ bv1 30)))
)
(define-fun max () (_ BitVec 30)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 30))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 30))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
