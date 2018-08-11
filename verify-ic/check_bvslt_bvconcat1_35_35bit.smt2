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
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 35))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 35))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 35))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
