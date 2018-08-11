(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 47))
(declare-fun tx () (_ BitVec 47))
(declare-fun ts () (_ BitVec 47))

(define-fun min () (_ BitVec 47)
  (bvnot (bvlshr (bvnot (_ bv0 47)) (_ bv1 47)))
)
(define-fun max () (_ BitVec 47)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 47))) (= (concat x s) (concat tx ts))))
   (=> (exists ((x (_ BitVec 47))) (= (concat x s) (concat tx ts))) SC)
  )
 )
)
(check-sat)
