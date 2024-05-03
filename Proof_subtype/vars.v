Definition id := nat.

(* locally nameless for binders in terms and types/qualifiers *)
Inductive var : Type :=
| varF : id -> var (* free var (deBruijn level) *)
| varB : id -> var (* locally-bound variable (deBruijn index) *)
.

Notation "# i" := (varB i) (at level 0, right associativity).
Notation "$ i" := (varF i) (at level 0, right associativity).



Definition f := nat.  (* field *)

Definition m := nat.  (* method *)

Definition l := nat.  (* locations *)

Definition cn := nat.  (* class name *)
