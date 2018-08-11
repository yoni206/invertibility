(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 36))
(declare-fun tx () (_ BitVec 36))
(declare-fun ts () (_ BitVec 36))

(define-fun min () (_ BitVec 36)
  (bvnot (bvlshr (bvnot (_ bv0 36)) (_ bv1 36)))
)
(define-fun max () (_ BitVec 36)
  (bvnot min)
)

(define-fun SC () Bool
(= s ts)
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 36))) (= (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 36))) (= (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
