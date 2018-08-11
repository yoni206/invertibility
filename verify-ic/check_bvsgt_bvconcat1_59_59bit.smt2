(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 59))
(declare-fun tx () (_ BitVec 59))
(declare-fun ts () (_ BitVec 59))

(define-fun min () (_ BitVec 59)
  (bvnot (bvlshr (bvnot (_ bv0 59)) (_ bv1 59)))
)
(define-fun max () (_ BitVec 59)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 59)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 59))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 59))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
