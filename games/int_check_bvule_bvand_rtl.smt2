(set-logic UFNIA)

(declare-fun intand (Int Int Int) Int)
(define-fun l ((k Int) (x Int) (s Int) (t Int)) Bool  (<= (intand k x s) t))
(define-fun SC ((k Int) (s Int) (t Int)) Bool true)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; what to prove            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun k () Int)
(declare-fun s () Int)
(declare-fun t () Int)




;<BEGIN_RTL>
;skolemized x for the right-to-left direction
(declare-fun x0 () Int)


(define-fun not_right_to_left ((k Int) (s Int) (t Int)) Bool (and (l k x0 s t) (not (SC k s t))))

(define-fun assertion_rtl () Bool (not_right_to_left k s t))
;<END_RTL>

(assert assertion_rtl)

(check-sat)
