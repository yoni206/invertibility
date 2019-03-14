(define-fun is_bv_width ((k Int)) Bool
 (and
  (> k 0)
  (and_is_ok k)
  (or_is_ok k)
  (xor_is_ok k)
 )
)

(define-fun is_bv_var ((k Int) (x Int)) Bool (in_range k x))
