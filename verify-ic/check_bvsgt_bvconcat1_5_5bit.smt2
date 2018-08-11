(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 5))
(declare-fun tx () (_ BitVec 5))
(declare-fun ts () (_ BitVec 5))

(define-fun min () (_ BitVec 5)
  (bvnot (bvlshr (bvnot (_ bv0 5)) (_ bv1 5)))
)
(define-fun max () (_ BitVec 5)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 5)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 5))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 5))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
