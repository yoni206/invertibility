(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 30))
(declare-fun tx () (_ BitVec 36))
(declare-fun ts () (_ BitVec 30))

(define-fun min () (_ BitVec 36)
  (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36)))
)
(define-fun max () (_ BitVec 36)
  (bvnot min)
)

(define-fun SC () Bool
(=> (= tx min) (bvule s ts))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 36))) (bvsle (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 36))) (bvsle (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
