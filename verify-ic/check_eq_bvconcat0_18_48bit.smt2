(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 48))
(declare-fun tx () (_ BitVec 18))
(declare-fun ts () (_ BitVec 48))

(define-fun min () (_ BitVec 18)
  (bvnot (bvlshr (bvnot (_ bv0 18)) (_ bv1 18)))
)
(define-fun max () (_ BitVec 18)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 18))) (= (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 18))) (= (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
