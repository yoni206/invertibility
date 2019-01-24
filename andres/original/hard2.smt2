;(s ·s) >>(s <<s) ̸≈ s · (s >>(s <<s)),
(declare-fun k () Int)
(declare-fun s () Int)
(define-fun left () Int (intlshr k (intmul k s s) (intshl k s s)))
(define-fun right () Int (intmul k s (intlshr k s (intshl k s s))))
(define-fun proposition () Bool (= left right))


(assert (> k 0))
(assert (in_range k s))
(assert two_to_the_is_ok)
(assert (not proposition))
(assert (< s k))

(check-sat)
