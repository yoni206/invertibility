(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 23))
(declare-fun tx () (_ BitVec 43))
(declare-fun ts () (_ BitVec 23))

(define-fun min () (_ BitVec 43)
  (bvnot (bvlshr (bvnot (_ bv0 43)) (_ bv1 43)))
)
(define-fun max () (_ BitVec 43)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 43)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 43))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 43))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
