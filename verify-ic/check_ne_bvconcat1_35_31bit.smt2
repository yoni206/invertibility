(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 31))
(declare-fun tx () (_ BitVec 35))
(declare-fun ts () (_ BitVec 31))

(define-fun min () (_ BitVec 35)
  (bvnot (bvlshr (bvnot (_ bv0 35)) (_ bv1 35)))
)
(define-fun max () (_ BitVec 35)
  (bvnot min)
)

(define-fun SC () Bool
true
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 35))) (distinct (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 35))) (distinct (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
