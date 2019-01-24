From BV Require Import BVList.

Import RAWBITVECTOR_LIST.

Require Import List Bool NArith Psatz (*Int63*) ZArith Nnat.

(* Practice:
 forall x : bitvector, size(x) >= 0*)
Theorem testbv : forall (x : bitvector), N.to_nat(size x) >= 0.
Proof.
induction x.
- auto.
- Admitted.


(*Addition*)
(* x + s = t <=> x = t - s *)
Theorem bvadd : forall (x s t : bitvector), iff ((bv_add x s) = t) (x = (bv_subt t s)).
Proof.
Admitted.


(*Multiplication*)
(* x.s = t <=> (-s | s) & t = t *)
Theorem bvmult_eq : forall (x s t : bitvector), iff ((bv_mult x s) = t) ((bv_and (bv_or (bv_not s) s) t) = t).
Proof.
Admitted.

(* x.s != t <=> s != 0 or t != 0 *)
Theorem bvmult_neq : forall (x s t : bitvector), iff 
  (~((bv_mult x s) = t)) 
  ((~(s = zeros (size s))) \/ (~(t = zeros (size t)))).


(*Mod*)
(* x mod s = t <=> ~(-s) >=u t *)

(* x mod s != t <=> s != 1 or t != 0 *)

(* s mod x = t <=> (t + t - s) & s >=u t *)

(* s mod x != t <=> s != 0 or t != 0 *)


(*Division*)
(* x / s = t <=> (s.t) / s = t *)

(* x / s != t <=>  s != 0 or t!= ~0*)

(* s / x = t <=> s / (s / t) = t *)

(* s / x != t  and size(s) = 1 <=> s & t = 0 *)

(* s / x != t  and size(s) != 1 <=> T *)


(*And*)
(* x & s = t <=> t & s = t*)
Theorem bvand_eq : forall (x s t : bitvector), iff ((bv_and x s) = t) ((bv_and t s) = t).
Proof.
Admitted.

(* x & s != t <=> s != 0 or t != 0 *)


(*Or*)
(* x | s = t <=> t & s = t *)
Theorem bvor_eq : forall (x s t  :bitvector), iff ((bv_or x s) = t) ((bv_and t s) = t).
Proof.
Admitted.

(* x | s != t <=> s != ~0 or t != ~0 *)


(*Logical right shift*)
(* x >> s = t <=> (t << s) >> s = t *)

(* x >> s != t <=> t != 0 or s <u size(s)*)

(* s >> x = t <=> [i=0...size(s)]OR(s >> i = t) *)

(* s >> x != t <=> s != 0 or t != 0 *)


(*Arithmetic right shift*)
(* x >>a s = t <=> 
  (s <u size(s) => (t << s) >>a s = t) and (s >=u size(s) => (t = ~0 or t = 0)) *)

(* x >>a s != t <=> T *)

(* s >>a x = t <=> [i=0...size(s)OR(s >>a i = t) *)

(* s >>a x != t <=> 
  (t != 0 or s!= 0) and (t != ~0 or s !- ~0) *)


(*Logical left shift*)
(* x << s = t <=> (t >> s) << s = t *)

(* x << s != t <=> t != 0 or s <u size(s) *)

(* s << x = t <=> [i=0...size(s)]OR(s << i = t)  *)

(* s << x != t <=> s != 0 or or t != 0 *)


(*Concat*)
(* x o s = t <=> s = t[size(s) - 1, 0] *)
Theorem bvconcat1_eq : forall (x s t : bitvector), iff ((bv_concat x s) = t) 
(s = extract t (N.to_nat(size(s)) - 1) (0)).
Proof.
Admitted.

(* x o s != t <=> T *)
Theorem bvconcat1_neq : forall (x s t : bitvector), iff (~((bv_concat x s) = t)) (True).
Proof.
intros x s t.
split. 
- intros H. reflexivity.
- intros H. Admitted.

(* s o x = t <=> s = t[size(t) - 1 : size(t) - size(s)] *)
Theorem bvconcat2_eq : forall (x s t : bitvector), iff ((bv_concat s x) = t) 
(s = extract t (N.to_nat(size(t)) - 1) 
               (N.to_nat(size(t)) - N.to_nat(size(s)))).
Proof. 
Admitted.

Theorem bvconcat2_neq : forall (x s t : bitvector), iff (~((bv_concat s x) = t)) (True).
Proof.
intros x s t.
split.
- intros H. reflexivity.
- intros H. Admitted.


