(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 48))
(declare-fun tx () (_ BitVec 48))
(declare-fun ts () (_ BitVec 48))

(define-fun min () (_ BitVec 48)
  (bvnot (bvlshr (bvnot (_ bv0 48)) (_ bv1 48)))
)
(define-fun max () (_ BitVec 48)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 48))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 48))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 48))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
