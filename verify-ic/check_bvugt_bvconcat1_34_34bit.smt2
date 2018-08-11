(set-logic BV)
(set-option :produce-models true)
(declare-fun s () (_ BitVec 34))
(declare-fun tx () (_ BitVec 34))
(declare-fun ts () (_ BitVec 34))

(define-fun min () (_ BitVec 34)
  (bvnot (bvlshr (bvnot (_ bv0 34)) (_ bv1 34)))
)
(define-fun max () (_ BitVec 34)
  (bvnot min)
)

(define-fun SC () Bool
(and (bvuge s ts) (=> (= s ts) (distinct tx (bvnot (_ bv0 34)))))
)

(assert
 (not
  (and
   (=> SC (exists ((x (_ BitVec 34))) (bvugt (concat s x) (concat ts tx))))
   (=> (exists ((x (_ BitVec 34))) (bvugt (concat s x) (concat ts tx))) SC)
  )
 )
)
(check-sat)
