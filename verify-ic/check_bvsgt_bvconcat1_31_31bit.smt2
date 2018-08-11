(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 31))
(declare-fun tx () (_ BitVec 31))
(declare-fun ts () (_ BitVec 31))

(define-fun min () (_ BitVec 31)
  (bvnot (bvlshr (bvnot (_ bv0 31)) (_ bv1 31)))
)
(define-fun max () (_ BitVec 31)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 31)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 31))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 31))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
