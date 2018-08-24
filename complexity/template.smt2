(set-logic BV)
(declare-fun s () (_ BitVec <n>))
(declare-fun t () (_ BitVec <n>))

(define-fun udivtotal ((a (_ BitVec <n>)) (b (_ BitVec <n>))) (_ BitVec <n>)
  (ite (= b (_ bv0 <n>)) (bvnot (_ bv0 <n>)) (bvudiv a b))
)
(define-fun uremtotal ((a (_ BitVec <n>)) (b (_ BitVec <n>))) (_ BitVec <n>)
  (ite (= b (_ bv0 <n>)) a (bvurem a b))
)
(define-fun min () (_ BitVec <n>)
  (bvnot (bvlshr (bvnot (_ bv0 <n>)) (_ bv1 <n>)))
)
(define-fun max () (_ BitVec <n>)
  (bvnot min)
)

<SC>

<l>

(assert
 (not
  (and
  (=> (SC s t) (exists ((x (_ BitVec <n>))) (l x s t)))
  (=> (exists ((x (_ BitVec <n>))) (l x s t)) (SC s t))
  )
 )
)
(check-sat)
