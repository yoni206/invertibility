(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 42))
(declare-fun tx () (_ BitVec 42))
(declare-fun ts () (_ BitVec 42))

(define-fun min () (_ BitVec 42)
  (bvnot (bvlshr (bvnot (_ bv0 42)) (_ bv1 42)))
)
(define-fun max () (_ BitVec 42)
  (bvnot min)
)

(define-fun SC () Bool
(bvsle s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 42))) (bvsle (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 42))) (bvsle (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
