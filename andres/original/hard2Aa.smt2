;(s ·s) >>(s <<s) ̸≈ s · (s >>(s <<s)),
(declare-fun k () Int)
(declare-fun s () Int)
(define-fun left () Int (intlshr k (intmul k s s) (intshl k s s)))
(define-fun right () Int 0)
(define-fun proposition () Bool (= left right))
(define-fun hint1 () Bool (=> (< (* s s) (two_to_the k)) (= (mod (* s s) (two_to_the k)) (* s s))))
(define-fun hint2 () Bool (=> (< (* s (two_to_the s)) (two_to_the k)) (= (mod (* s (two_to_the s)) (two_to_the k)) (* s (two_to_the s)))))
(define-fun hint3 () Bool (=> (< (* s s) (* s (two_to_the s))) (= (div (* s s) (* s (two_to_the s))) 0)))
(define-fun hint4 () Bool (=> (< s (* s (two_to_the s))) (= (div s (* s (two_to_the s))) 0)))

(assert (> k 3))
(assert (in_range k s))
(assert two_to_the_is_ok)
(assert hint1)
(assert hint2)
(assert hint3)
(assert hint4)
(assert (not proposition))

(assert (< s k))
(assert (< (* s s) (two_to_the k))) ;actually this follows from the next line
(assert (< (* s (two_to_the s)) (two_to_the k)))
(assert (< (* s s) (* (s (two_to_the s)))))
(assert (< s (* (s (two_to_the s)))))

(check-sat)
