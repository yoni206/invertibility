(define-fun two_to_the ((k Int)) Int (^ 2 k))
(assert (= 7 (two_to_the 3)))
(check-sat)
