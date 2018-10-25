From BV Require Import BVList.

(** You should now be able to flawlessly access any structure in
    the source BVList.v. *)

Goal forall (a b: list bool) c, length a = length b ->
     length a = length (RAWBITVECTOR_LIST.subst_list_borrow a b c) \/ False.
left. now apply RAWBITVECTOR_LIST.subst_list_borrow_length. Qed.

(** You can for sure import modules if you do not want to always
    use them as prefixes (RAWBITVECTOR_LIST, BITVECTOR_LIST, ...)
    here and there. *)

Import RAWBITVECTOR_LIST.

(** For instance, in the above goal, the prefix RAWBITVECTOR_LIST
    is no more required. But be careful in this case since there
    are many definitions and declerations that share the same name
    but placed in different modules. *)

Goal forall (a b: list bool) c, length a = length b ->
     length a = length (subst_list_borrow a b c) \/ False.
left. now apply subst_list_borrow_length. Qed.

