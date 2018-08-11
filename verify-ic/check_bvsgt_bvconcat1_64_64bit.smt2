(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 64))
(declare-fun tx () (_ BitVec 64))
(declare-fun ts () (_ BitVec 64))

(define-fun min () (_ BitVec 64)
  (bvnot (bvlshr (bvnot (_ bv0 64)) (_ bv1 64)))
)
(define-fun max () (_ BitVec 64)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 64)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 64))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 64))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
