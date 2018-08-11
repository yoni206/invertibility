(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 19))
(declare-fun tx () (_ BitVec 47))
(declare-fun ts () (_ BitVec 19))

(define-fun min () (_ BitVec 47)
  (bvnot (bvlshr (bvnot (_ bv0 47)) (_ bv1 47)))
)
(define-fun max () (_ BitVec 47)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 47)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 47))) (bvsgt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 47))) (bvsgt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
