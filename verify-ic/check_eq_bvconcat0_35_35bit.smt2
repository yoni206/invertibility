(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 35))
(declare-fun tx () (_ BitVec 35))
(declare-fun ts () (_ BitVec 35))

(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 35))) (= (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 35))) (= (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
