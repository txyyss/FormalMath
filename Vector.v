Require Import Coq.Reals.Reals.
Require Import FormalMath.lib.dep_list.

Definition Vector (n: nat) := dep_list R n.

Section N_DIMENSION.

  Context {n : nat}.

  Definition vec_dot_prod (v1 v2: Vector n) :=
    dep_fold_left Rplus (dep_binop Rmult v1 v2) 0%R.

  Definition vec_add (v1 v2: Vector n) := dep_binop Rplus v1 v2.

End N_DIMENSION.
