(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 15))
(declare-fun tx () (_ BitVec 51))
(declare-fun ts () (_ BitVec 15))

(define-fun min () (_ BitVec 51)
  (bvnot (bvlshr (bvnot (_ bv0 51)) (_ bv1 51)))
)
(define-fun max () (_ BitVec 51)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvsle s ts) (=> (= s ts) (distinct tx (_ bv0 51))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 51))) (bvslt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 51))) (bvslt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
